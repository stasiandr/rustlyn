//! Hot patches: a changed method written again as a static method of a class
//! of its own, in C#, to be compiled against the assembly it patches.
//!
//! An instance method becomes a static one taking the instance first, which
//! is how the runtime passes it anyway, so the old method's code can jump to
//! the new one. Inside the body, whatever named a member of the instance
//! without saying whose is given `self.`, `this` becomes `self`, and a static
//! member or a nested type named as the class's own is named from the global
//! namespace. The patch is compiled in the namespace the class was declared
//! in, with the using directives of its file, so everything else resolves as
//! it did.
//!
//! The patched assembly has every member opened to the assembly and names
//! the patch as a friend (`InternalsVisibleTo("PilotPatch")`), so a private
//! member the body uses is reachable from the patch.

use std::collections::{BTreeMap, HashMap, HashSet};

use rustlyn_semantics::{
    Binder, BodyBinder, BoundBody, BoundSymbol, Compilation, Diagnostics, MethodKind, Modifiers,
    RefKind, SymbolId, SymbolKind, Type, TypeKind,
};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::diff::Changes;

/// One method the patch replaces, as reflection names it.
pub(crate) struct Entry {
    /// `Namespace.Outer+Inner`.
    pub(crate) original_type: String,
    pub(crate) method: String,
    /// The `Type.Name` of each parameter: `Int32`, `List``1`, `Entity&`.
    pub(crate) parameters: Vec<String>,
    pub(crate) patch_type: String,
    pub(crate) patch_method: String,
}

pub(crate) struct PatchSource {
    pub(crate) text: String,
    pub(crate) entries: Vec<Entry>,
}

/// The C# of a patch for `changes`, or why one cannot be made.
pub(crate) fn write(
    compilation: &Compilation,
    changes: &Changes,
    round: usize,
    tails: &HashMap<SymbolId, u32>,
    assembly: Option<&HashSet<String>>,
) -> Result<PatchSource, String> {
    let binder = Binder::new(compilation);
    let symbols = compilation.symbols();
    // A class of another assembly: one read from metadata, or one compiled
    // here from a file the patched assembly does not have — a package's,
    // which an editor's compilation of the project holds as source.
    let trees = compilation.trees();
    let foreign = |owner: SymbolId| -> bool {
        if compilation.declaration_node(owner).is_none() {
            return true;
        }
        let Some(files) = assembly else { return false };
        symbols.get(owner).locations.iter().all(|location| {
            trees
                .source(location.tree)
                .is_none_or(|source| !files.contains(source.name()))
        })
    };
    let added_methods: HashSet<SymbolId> = changes.added_methods.iter().copied().collect();
    let mut added_fields: HashSet<SymbolId> = changes.added_fields.iter().copied().collect();
    // Constants are written where they are read: nothing keeps them.
    let constant = |field: SymbolId| {
        symbols.get(field).modifiers.contains(Modifiers::CONST)
            || symbols
                .get(field)
                .container
                .is_some_and(|owner| symbols.get(owner).type_kind() == Some(TypeKind::Enum))
    };
    // A property the edit added is a field where it is only storage, and is
    // read through its getter where it has one.
    let mut computed: HashMap<SymbolId, SymbolId> = HashMap::new();
    // And written through its setter, where it declares one with a body.
    let mut setters: HashMap<SymbolId, SymbolId> = HashMap::new();
    for &property in &changes.added_properties {
        if is_stored(compilation, property) {
            added_fields.insert(property);
        } else {
            let detail = symbols
                .get(property)
                .as_property()
                .ok_or("a property without its detail")?;
            if detail.is_indexer {
                return Err(format!(
                    "{}: an added indexer needs a reload",
                    symbols.qualified_name(property)
                ));
            }
            if let Some(setter) = detail.setter {
                setters.insert(property, setter);
            }
            computed.insert(property, detail.getter.unwrap_or(property));
        }
    }
    let added_methods: HashSet<SymbolId> = added_methods
        .into_iter()
        .chain(computed.values().copied())
        .chain(setters.values().copied())
        .collect();
    // A type the edit added inside another lives in a holder of the patch's
    // own, `__PilotNest_Outer`, which sees the outer type's statics through
    // `using static`: what named it names the holder's.
    let mut nested: HashMap<SymbolId, String> = HashMap::new();
    for &ty in &changes.added_types {
        if let Some(outer) = symbols
            .get(ty)
            .container
            .filter(|container| symbols.get(*container).kind == SymbolKind::NamedType)
        {
            if generic_around(compilation, outer) {
                return Err(format!(
                    "{}: a type added inside a generic one needs a reload",
                    symbols.qualified_name(ty)
                ));
            }
            let namespace = holder_namespace(compilation, outer);
            let holder = format!("__PilotNest_{}", type_path(compilation, outer).join("_"));
            let qualified = format!("global::{namespace}.{holder}.{}", symbols.get(ty).name);
            nested.insert(ty, qualified);
        }
    }
    // A struct has no identity to hang a field on: kept beside a boxed copy,
    // the field would be written and lost. It lives in the struct's tail,
    // where it has one (see `tails.rs`).
    for &field in &added_fields {
        if let Some(owner) = symbols.get(field).container
            && symbols.get(owner).type_kind() == Some(TypeKind::Struct)
            && !symbols.get(field).modifiers.contains(Modifiers::STATIC)
            && !constant(field)
            && !tails.contains_key(&field)
        {
            return Err(format!(
                "{}: a field added to a struct without a tail needs a reload",
                symbols.qualified_name(field)
            ));
        }
    }
    let methods: Vec<SymbolId> = changes
        .bodies
        .iter()
        .chain(&changes.added_methods)
        .chain(computed.values())
        .chain(setters.values())
        .copied()
        .collect();

    // Where each method will live, decided before any body is written: a body
    // calling a method the edit added calls it there.
    let mut placed: HashMap<SymbolId, (String, String, String)> = HashMap::new();
    let mut counts: HashMap<String, usize> = HashMap::new();
    for &id in &methods {
        let owner = owner_of(compilation, id, added_methods.contains(&id))?;
        let namespace = namespace_of(compilation, owner);
        let class = format!(
            "__PilotPatch_{}_{round}",
            type_path(compilation, owner).join("_")
        );
        let global = if namespace.is_empty() {
            format!("global::{class}")
        } else {
            format!("global::{namespace}.{class}")
        };
        let count = counts.entry(global.clone()).or_insert(0);
        // `.ctor` is no name C# can write.
        let method = format!("{}__{count}", symbols.get(id).name.replace('.', ""));
        *count += 1;
        placed.insert(id, (namespace, class, method));
    }
    let place = |id: SymbolId| -> String {
        let (namespace, class, method) = &placed[&id];
        if namespace.is_empty() {
            format!("global::{class}.{method}")
        } else {
            format!("global::{namespace}.{class}.{method}")
        }
    };

    let mut usings: Vec<String> = Vec::new();
    let mut classes: BTreeMap<(String, String), Vec<String>> = BTreeMap::new();
    let mut entries = Vec::new();

    // An added field's first value: its initializer, or what a constructor
    // gave it — written as a method of the patch, run when the field is
    // first read on an object that has not had it.
    let mut first_values: Vec<(SymbolId, SyntaxNode, SymbolId, usize)> = Vec::new();
    let mut converted_first: Vec<SymbolId> = Vec::new();
    for &field in &added_fields {
        if tails.contains_key(&field) || constant(field) {
            continue;
        }
        let Some(declarator) = compilation.declaration_node(field) else {
            continue;
        };
        let Some(&(tree, _)) = compilation.declaration_nodes(field).first() else {
            continue;
        };
        if changes.converted.contains(&field) {
            converted_first.push(field);
        } else if let Some(value) = declarator
            .children()
            .find(|child| child.kind() == SyntaxKind::EqualsValueClause)
            .and_then(|clause| clause.children().last())
        {
            first_values.push((field, value, field, tree));
        } else if let Some(&(_, constructor, statement)) = changes
            .assigned
            .iter()
            .find(|(assigned, _, _)| *assigned == field)
            && let Some(value) = compilation
                .declaration_node(constructor)
                .and_then(|node| node.find_node(statement))
                .and_then(|statement| {
                    statement
                        .descendants()
                        .find(|node| node.kind() == SyntaxKind::SimpleAssignmentExpression)
                })
                .and_then(|assignment| assignment.children().last())
            && let Some(&(tree, _)) = compilation.declaration_nodes(constructor).first()
        {
            first_values.push((field, value, constructor, tree));
        }
    }
    // A value made from a constructor parameter nothing kept cannot be made
    // again: the field starts empty on an object made before the patch.
    first_values.retain(|(field, value, from, tree)| {
        if from == field {
            return true;
        }
        let Some(declaration) = compilation.declaration_node(*from) else {
            return false;
        };
        let bound = BodyBinder::bind_member(&binder, *tree, &declaration);
        let kept = kept_parameters(compilation, &declaration, &bound, &added_fields, true);
        !names_a_lost_parameter(value, &bound, symbols, &kept)
    });
    let mut initializers: HashMap<SymbolId, String> = HashMap::new();
    // A serialized field given another type starts from the loaded one's
    // value, converted at run time (`PilotRuntime.Fields.Former`).
    for &field in &converted_first {
        let owner = symbols
            .get(field)
            .container
            .ok_or("a field outside a type")?;
        let ty = type_text(compilation, &binder.type_of(field, &mut Diagnostics::new()))?;
        let namespace = namespace_of(compilation, owner);
        let class = format!(
            "__PilotPatch_{}_{round}",
            type_path(compilation, owner).join("_")
        );
        let method = format!("{}__first", symbols.get(field).name);
        classes.entry((namespace.clone(), class.clone())).or_default().push(format!(
            "        public static {ty} {method}(object owner) => global::PilotRuntime.Fields.Former<{ty}>(owner, \"{}\");\n",
            symbols.get(field).name
        ));
        initializers.insert(
            field,
            if namespace.is_empty() {
                format!("global::{class}.{method}")
            } else {
                format!("global::{namespace}.{class}.{method}")
            },
        );
    }
    for &(field, ..) in &first_values {
        let owner = symbols
            .get(field)
            .container
            .ok_or("a field outside a type")?;
        let namespace = namespace_of(compilation, owner);
        let class = format!(
            "__PilotPatch_{}_{round}",
            type_path(compilation, owner).join("_")
        );
        let method = format!("{}__first", symbols.get(field).name);
        let global = if namespace.is_empty() {
            format!("global::{class}.{method}")
        } else {
            format!("global::{namespace}.{class}.{method}")
        };
        initializers.insert(field, global);
    }
    for (field, value, from, tree) in &first_values {
        let field = *field;
        let name = symbols.qualified_name(field);
        let owner = symbols
            .get(field)
            .container
            .ok_or("a field outside a type")?;
        let is_static = symbols.get(field).modifiers.contains(Modifiers::STATIC);
        let declaration = compilation
            .declaration_node(*from)
            .ok_or_else(|| format!("{name} has no declaration"))?;
        let bound = BodyBinder::bind_member(&binder, *tree, &declaration);
        let kept = kept_parameters(
            compilation,
            &declaration,
            &bound,
            &added_fields,
            *from != field,
        );
        let rewriter = Rewriter {
            compilation,
            binder: &binder,
            foreign: &foreign,
            added_fields: &added_fields,
            added_methods: &added_methods,
            computed: &computed,
            setters: &setters,
            nested: &nested,
            tails,
            place: &place,
            initializers: &initializers,
            bound: &bound,
            name: &name,
            is_static,
            owner: Some(owner),
            tree: *tree,
            copied: false,
            substitute: (*from != field).then_some(&kept),
        };
        let edits = rewriter.edits(value)?;
        let ty = type_text(compilation, &binder.type_of(field, &mut Diagnostics::new()))?;
        // `string[] names = { "a" };` says what it makes only beside the
        // field: on its own it is `new string[] { "a" }`.
        let text = if value.kind() == SyntaxKind::ArrayInitializerExpression {
            format!("new {ty} {}", apply(value, edits))
        } else {
            apply(value, edits)
        };
        collect_usings(compilation, *tree, &mut usings);
        let method = format!("{}__first", symbols.get(field).name);
        let namespace = namespace_of(compilation, owner);
        let class = format!(
            "__PilotPatch_{}_{round}",
            type_path(compilation, owner).join("_")
        );
        let written = if is_static {
            format!("        public static {ty} {method}() => {text};\n")
        } else {
            format!(
                "        public static {ty} {method}(object owner)\n        {{\n            var self = ({})owner;\n            return {text};\n        }}\n",
                global_name(compilation, owner)
            )
        };
        classes.entry((namespace, class)).or_default().push(written);
    }

    // What runs once when the patch is applied: a static field's changed
    // initializer, given to the loaded field, and a static constructor
    // whose body changed.
    for &id in changes.reinitialized.iter().chain(&changes.rerun) {
        let name = symbols.qualified_name(id);
        let owner = symbols.get(id).container.ok_or("a member outside a type")?;
        let &(tree, _) = compilation
            .declaration_nodes(id)
            .first()
            .ok_or_else(|| format!("{name} has no declaration"))?;
        let declaration = compilation
            .declaration_node(id)
            .ok_or_else(|| format!("{name} has no declaration"))?;
        let bound = BodyBinder::bind_member(&binder, tree, &declaration);
        let rewriter = Rewriter {
            compilation,
            binder: &binder,
            foreign: &foreign,
            added_fields: &added_fields,
            added_methods: &added_methods,
            computed: &computed,
            setters: &setters,
            nested: &nested,
            tails,
            place: &place,
            initializers: &initializers,
            bound: &bound,
            name: &name,
            is_static: true,
            owner: Some(owner),
            tree,
            copied: false,
            substitute: None,
        };
        let body = if symbols.get(id).kind == SymbolKind::Field {
            let value = declaration
                .children()
                .find(|child| child.kind() == SyntaxKind::EqualsValueClause)
                .and_then(|clause| clause.children().last())
                .ok_or_else(|| format!("{name} has no initializer to give it"))?;
            let edits = rewriter.edits(&value)?;
            let ty = type_text(compilation, &binder.type_of(id, &mut Diagnostics::new()))?;
            let text = if value.kind() == SyntaxKind::ArrayInitializerExpression {
                format!("new {ty} {}", apply(&value, edits))
            } else {
                apply(&value, edits)
            };
            format!(
                "{{\n            {}.{} = {text};\n        }}",
                global_name(compilation, owner),
                symbols.get(id).name
            )
        } else {
            let block = declaration
                .children()
                .find(|child| child.kind() == SyntaxKind::Block)
                .ok_or_else(|| format!("{name} has no body"))?;
            let edits = rewriter.edits(&block)?;
            apply(&block, edits)
        };
        collect_usings(compilation, tree, &mut usings);
        let namespace = namespace_of(compilation, owner);
        let class = format!(
            "__PilotPatch_{}_{round}",
            type_path(compilation, owner).join("_")
        );
        let method = format!("{}__again", symbols.get(id).name.replace('.', ""));
        classes
            .entry((namespace.clone(), class.clone()))
            .or_default()
            .push(format!(
                "        public static void {method}()\n        {body}\n"
            ));
        entries.push(Entry {
            original_type: "!run".to_string(),
            method: name.clone(),
            parameters: Vec::new(),
            patch_type: if namespace.is_empty() {
                class
            } else {
                format!("{namespace}.{class}")
            },
            patch_method: method,
        });
    }

    for &id in &methods {
        let symbol = symbols.get(id);
        let name = symbols.qualified_name(id);
        // `int P => e;` is its own getter: `get_P`, taking nothing.
        let getter_of_its_own = symbol.kind == SymbolKind::Property;
        let declared_parameters: Vec<SymbolId> = if getter_of_its_own {
            Vec::new()
        } else {
            symbol
                .as_method()
                .ok_or_else(|| format!("{name} is not a method"))?
                .parameters
                .clone()
        };
        let owner = owner_of(compilation, id, added_methods.contains(&id))?;
        let is_static = symbol.modifiers.contains(Modifiers::STATIC);
        let &(tree, _) = compilation
            .declaration_nodes(id)
            .first()
            .ok_or_else(|| format!("{name} has no declaration"))?;
        let node = compilation
            .declaration_node(id)
            .ok_or_else(|| format!("{name} has no declaration"))?;
        let body = node
            .children()
            .find(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::Block | SyntaxKind::ArrowExpressionClause
                )
            })
            .ok_or_else(|| format!("{name} has no body"))?;
        let bound = BodyBinder::bind_member(&binder, tree, &node);
        collect_usings(compilation, tree, &mut usings);

        let rewriter = Rewriter {
            compilation,
            binder: &binder,
            foreign: &foreign,
            added_fields: &added_fields,
            added_methods: &added_methods,
            computed: &computed,
            setters: &setters,
            nested: &nested,
            tails,
            place: &place,
            initializers: &initializers,
            bound: &bound,
            name: &name,
            is_static,
            owner: Some(owner),
            tree,
            copied: false,
            substitute: None,
        };
        let edits = rewriter.edits(&body)?;
        // What a class's constructor chains to, which the patch calls too.
        let chain = if symbol
            .as_method()
            .is_some_and(|method| method.method_kind == MethodKind::Constructor)
            && symbols.get(owner).type_kind() == Some(TypeKind::Class)
        {
            constructor_chain(compilation, &binder, &bound, &node, owner, &rewriter)?
        } else {
            None
        };
        let rewritten = apply(&body, edits);
        let body_text = if body.kind() == SyntaxKind::ArrowExpressionClause {
            format!("{rewritten};")
        } else {
            rewritten
        };
        // A class's constructor runs the class's field initializers before
        // its body; the patch that stands in for it does too.
        let body_text = if symbol
            .as_method()
            .is_some_and(|method| method.method_kind == MethodKind::Constructor)
            && symbols.get(owner).type_kind() == Some(TypeKind::Class)
        {
            let mut initializing = String::new();
            for member in symbols.iter().filter(|member| {
                member.container == Some(owner)
                    && matches!(member.kind, SymbolKind::Field | SymbolKind::Property)
                    && !member.modifiers.contains(Modifiers::STATIC)
                    && !member.modifiers.contains(Modifiers::CONST)
                    && !added_fields.contains(&member.id)
            }) {
                let Some(declarator) = compilation.declaration_node(member.id) else {
                    continue;
                };
                let Some(value) = declarator
                    .children()
                    .find(|child| child.kind() == SyntaxKind::EqualsValueClause)
                    .and_then(|clause| clause.children().last())
                else {
                    continue;
                };
                if member.kind == SymbolKind::Property
                    && member
                        .as_property()
                        .is_some_and(|detail| !detail.has_set && !detail.has_init)
                {
                    return Err(format!(
                        "{name}: {} has an initializer and no setter to give it from outside",
                        member.name
                    ));
                }
                let Some(&(member_tree, _)) = compilation.declaration_nodes(member.id).first()
                else {
                    continue;
                };
                let bound = BodyBinder::bind_member(&binder, member_tree, &declarator);
                let rewriter = Rewriter {
                    compilation,
                    binder: &binder,
                    foreign: &foreign,
                    added_fields: &added_fields,
                    added_methods: &added_methods,
                    computed: &computed,
                    setters: &setters,
                    nested: &nested,
                    tails,
                    place: &place,
                    initializers: &initializers,
                    bound: &bound,
                    name: &name,
                    is_static: false,
                    owner: Some(owner),
                    tree: member_tree,
                    copied: false,
                    substitute: None,
                };
                let edits = rewriter.edits(&value)?;
                let text = if value.kind() == SyntaxKind::ArrayInitializerExpression {
                    let ty = type_text(
                        compilation,
                        &binder.type_of(member.id, &mut Diagnostics::new()),
                    )?;
                    format!("new {ty} {}", apply(&value, edits))
                } else {
                    apply(&value, edits)
                };
                collect_usings(compilation, member_tree, &mut usings);
                initializing.push_str(&format!("\n            self.{} = {text};", member.name));
            }
            // `: this(...)` runs the other constructor, initializers and
            // all; anything else runs them, then the base's constructor.
            let initializing = match &chain {
                Some((call, true)) => format!("\n            {call}"),
                Some((call, false)) => format!("{initializing}\n            {call}"),
                None => initializing,
            };
            if body.kind() == SyntaxKind::ArrowExpressionClause {
                let expression = body_text.trim_start().trim_start_matches("=>");
                format!("{{{initializing}\n            {expression}\n        }}")
            } else {
                let open = body_text.find('{').map_or(0, |at| at + 1);
                format!("{}{initializing}{}", &body_text[..open], &body_text[open..])
            }
        } else {
            body_text
        };

        let mut diagnostics = Diagnostics::new();
        let returns = binder.type_of(id, &mut diagnostics);
        let mut parameters = Vec::new();
        let mut reflected = Vec::new();
        if !is_static {
            let by_reference = symbols.get(owner).type_kind() == Some(TypeKind::Struct);
            parameters.push(format!(
                "{}{} self",
                if by_reference { "ref " } else { "" },
                global_name(compilation, owner)
            ));
        }
        for &parameter in &declared_parameters {
            let symbol = symbols.get(parameter);
            let Some(written) = symbol.as_parameter() else {
                continue;
            };
            let ty = binder.type_of(parameter, &mut diagnostics);
            let (keyword, by_reference) = match written.ref_kind {
                RefKind::None => ("", false),
                RefKind::Ref => ("ref ", true),
                RefKind::Out => ("out ", true),
                RefKind::In => ("in ", true),
            };
            let params = if written.is_params { "params " } else { "" };
            // What a call may leave out, it may leave out of the patch's too.
            let default = compilation
                .declaration_node(parameter)
                .and_then(|node| {
                    node.children()
                        .find(|child| child.kind() == SyntaxKind::EqualsValueClause)
                        .map(|clause| format!(" {}", clause.text().trim()))
                })
                .unwrap_or_default();
            parameters.push(format!(
                "{params}{keyword}{} {}{default}",
                type_text(compilation, &ty)?,
                symbol.name
            ));
            reflected.push(format!(
                "{}{}",
                reflection_name(compilation, &ty),
                if by_reference { "&" } else { "" }
            ));
        }
        let constructor = symbol
            .as_method()
            .is_some_and(|method| method.method_kind == MethodKind::Constructor);
        let returns_text = match &returns {
            _ if constructor => "void".to_string(),
            Type::ByRef(inner) => format!("ref {}", type_text(compilation, inner)?),
            other => type_text(compilation, other)?,
        };
        let mut modifiers = "public static".to_string();
        if symbol.modifiers.contains(Modifiers::ASYNC) {
            modifiers.push_str(" async");
        }
        // `unsafe` on the type around the method made its body unsafe too.
        let mut around = Some(owner);
        let mut unsafe_type = false;
        while let Some(ty) = around {
            if symbols.get(ty).kind != SymbolKind::NamedType {
                break;
            }
            unsafe_type |= symbols.get(ty).modifiers.contains(Modifiers::UNSAFE);
            around = symbols.get(ty).container;
        }
        if symbol.modifiers.contains(Modifiers::UNSAFE) || unsafe_type {
            modifiers.push_str(" unsafe");
        }

        let (namespace, class, method) = placed[&id].clone();
        // A generic method the edit added keeps its type parameters and what
        // constrains them, as written.
        let generics = symbol
            .as_method()
            .filter(|detail| !detail.type_parameters.is_empty())
            .map(|detail| {
                let names: Vec<&str> = detail
                    .type_parameters
                    .iter()
                    .map(|parameter| symbols.get(*parameter).name.as_str())
                    .collect();
                format!("<{}>", names.join(", "))
            })
            .unwrap_or_default();
        let constraints: String = node
            .children()
            .filter(|child| child.kind() == SyntaxKind::TypeParameterConstraintClause)
            .map(|clause| format!(" {}", clause.text().trim()))
            .collect();
        classes
            .entry((namespace.clone(), class.clone()))
            .or_default()
            .push(format!(
                "        {modifiers} {returns_text} {method}{generics}({}){constraints}\n        {body_text}\n",
                parameters.join(", ")
            ));
        // A method the edit added replaces nothing: it is only called, from
        // the patch.
        if !added_methods.contains(&id) {
            entries.push(Entry {
                original_type: symbols.metadata_qualified_name(owner),
                method: if getter_of_its_own {
                    format!("get_{}", symbol.name)
                } else {
                    symbol.name.clone()
                },
                parameters: reflected,
                patch_type: if namespace.is_empty() {
                    class.clone()
                } else {
                    format!("{namespace}.{class}")
                },
                patch_method: method,
            });
        }
    }

    // A type the loaded assembly lacks comes whole: it is the patch's own.
    let mut types: BTreeMap<String, Vec<String>> = BTreeMap::new();
    // Holders by outer type: its namespace, its global name, the holder's
    // name, and the types it holds.
    let mut holders: BTreeMap<String, (String, String, String, Vec<String>)> = BTreeMap::new();
    // A type the edit added comes with every part of it — the file that
    // declares it and what the generators wrote for it — and once, however
    // many of its files the edit touched.
    let mut copied: HashSet<SymbolId> = HashSet::new();
    for &ty in &changes.added_types {
        if !copied.insert(ty) {
            continue;
        }
        // Each part as the patch writes it: what its members name of the
        // edit's other additions rewritten, every type named in full.
        let mut parts: Vec<(String, String)> = Vec::new();
        for &(tree, span) in compilation.declaration_nodes(ty) {
            let node = compilation
                .trees()
                .get(tree)
                .and_then(|tree| tree.root().find_node(span))
                .ok_or_else(|| format!("{} has no declaration", symbols.qualified_name(ty)))?;
            collect_usings(compilation, tree, &mut usings);
            let mut edits: Vec<(TextSpan, String)> = Vec::new();
            for member in node.descendants().filter(|member| {
                matches!(
                    member.kind(),
                    SyntaxKind::MethodDeclaration
                        | SyntaxKind::ConstructorDeclaration
                        | SyntaxKind::DestructorDeclaration
                        | SyntaxKind::OperatorDeclaration
                        | SyntaxKind::ConversionOperatorDeclaration
                        | SyntaxKind::GetAccessorDeclaration
                        | SyntaxKind::SetAccessorDeclaration
                        | SyntaxKind::InitAccessorDeclaration
                        | SyntaxKind::AddAccessorDeclaration
                        | SyntaxKind::RemoveAccessorDeclaration
                        | SyntaxKind::PropertyDeclaration
                ) || (member.kind() == SyntaxKind::VariableDeclarator
                    && member
                        .children()
                        .any(|child| child.kind() == SyntaxKind::EqualsValueClause))
            }) {
                let Some(declared) = compilation.declared_symbol(tree, member.span()) else {
                    continue;
                };
                let member_owner = symbols.get(declared).container.unwrap_or(ty);
                let member_owner = if symbols.get(member_owner).kind == SymbolKind::NamedType {
                    member_owner
                } else {
                    symbols.get(member_owner).container.unwrap_or(ty)
                };
                let name = symbols.qualified_name(declared);
                let bound = BodyBinder::bind_member(&binder, tree, &member);
                let rewriter = Rewriter {
                    compilation,
                    binder: &binder,
                    foreign: &foreign,
                    added_fields: &added_fields,
                    added_methods: &added_methods,
                    computed: &computed,
                    setters: &setters,
                    nested: &nested,
                    tails,
                    place: &place,
                    initializers: &initializers,
                    bound: &bound,
                    name: &name,
                    is_static: symbols.get(declared).modifiers.contains(Modifiers::STATIC),
                    owner: Some(member_owner),
                    tree,
                    copied: true,
                    substitute: None,
                };
                // What is not a body — a property's accessors are bound on
                // their own — is left to them.
                let region = match member.kind() {
                    SyntaxKind::PropertyDeclaration => member.children().find(|child| {
                        matches!(
                            child.kind(),
                            SyntaxKind::ArrowExpressionClause | SyntaxKind::EqualsValueClause
                        )
                    }),
                    SyntaxKind::VariableDeclarator => member
                        .children()
                        .find(|child| child.kind() == SyntaxKind::EqualsValueClause),
                    _ => member.children().find(|child| {
                        matches!(
                            child.kind(),
                            SyntaxKind::Block | SyntaxKind::ArrowExpressionClause
                        )
                    }),
                };
                if let Some(region) = region {
                    edits.extend(rewriter.edits(&region)?);
                }
            }
            edits.sort_by_key(|(span, _)| (span.start(), span.length()));
            edits.dedup_by_key(|(span, _)| *span);
            let text = node.text();
            let start = node.span().start();
            // The head — modifiers and all, before `class` — is opened
            // apart from the rest, so the keyword is found where it stands.
            let keyword = node
                .child_tokens()
                .find(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::ClassKeyword
                            | SyntaxKind::StructKeyword
                            | SyntaxKind::InterfaceKeyword
                            | SyntaxKind::EnumKeyword
                            | SyntaxKind::RecordKeyword
                            | SyntaxKind::DelegateKeyword
                    )
                })
                .map_or(start, |token| token.span().start());
            let (head, rest): (Vec<_>, Vec<_>) = edits
                .into_iter()
                .partition(|(span, _)| span.start() < keyword);
            let head_text = apply_text(&text, start, TextSpan::new(start, keyword - start), head);
            let rest_text = apply_text(
                &text,
                start,
                TextSpan::new(keyword, node.span().end() - keyword),
                rest,
            );
            parts.push((head_text, rest_text));
        }
        if let Some(outer) = symbols
            .get(ty)
            .container
            .filter(|container| symbols.get(*container).kind == SymbolKind::NamedType)
        {
            let holder = format!("__PilotNest_{}", type_path(compilation, outer).join("_"));
            holders
                .entry(global_name(compilation, outer))
                .or_insert_with(|| {
                    (
                        holder_namespace(compilation, outer),
                        global_name(compilation, outer),
                        holder,
                        Vec::new(),
                    )
                })
                .3
                .extend(
                    parts
                        .iter()
                        .map(|(head, rest)| format!("{}{rest}", opened_head(head))),
                );
            continue;
        }
        types
            .entry(namespace_of(compilation, ty))
            .or_default()
            .extend(parts.iter().map(|(head, rest)| format!("{head}{rest}")));
    }

    let mut text = String::new();
    for using in &usings {
        text.push_str(using);
        text.push('\n');
    }
    let mut namespaces: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for ((namespace, class), methods) in &classes {
        let mut block = format!("    public static class {class}\n    {{\n");
        for method in methods {
            block.push_str(method);
        }
        block.push_str("    }\n");
        namespaces.entry(namespace.clone()).or_default().push(block);
    }
    for (namespace, declared) in types {
        namespaces.entry(namespace).or_default().extend(declared);
    }
    for (namespace, blocks) in &namespaces {
        let open = !namespace.is_empty();
        if open {
            text.push_str(&format!("namespace {namespace}\n{{\n"));
        }
        for block in blocks {
            text.push_str(block);
            text.push('\n');
        }
        if open {
            text.push_str("}\n");
        }
    }
    // Each holder in a namespace block of its own, so that what `using
    // static` brings in reaches no other code of the patch.
    for (namespace, outer, holder, held) in holders.values() {
        let body = format!(
            "    using static {outer};\n    internal static class {holder}\n    {{\n{}\n    }}\n",
            held.join("\n")
        );
        text.push_str(&format!("namespace {namespace}\n{{\n{body}}}\n"));
    }
    Ok(PatchSource { text, entries })
}

/// The call a class's patched constructor makes to the constructor it
/// chains to, and whether that is one of its own (`: this(...)`), which runs
/// the field initializers itself. `None` where the base is `object`.
fn constructor_chain(
    compilation: &Compilation,
    binder: &Binder,
    bound: &BoundBody,
    node: &SyntaxNode,
    owner: SymbolId,
    rewriter: &Rewriter,
) -> Result<Option<(String, bool)>, String> {
    let symbols = compilation.symbols();
    let name = symbols.qualified_name(owner);
    let call = |target: &Type,
                parameters: &[String],
                arguments: &[String]|
     -> Result<String, String> {
        if parameters.len() > 15 {
            return Err(format!(
                "{name}: a constructor chained to with too many parameters"
            ));
        }
        let target = type_text(compilation, target)?;
        let mut all = vec![target.clone()];
        all.extend(parameters.iter().cloned());
        let types: Vec<String> = parameters
            .iter()
            .map(|ty| format!("typeof({ty})"))
            .collect();
        let passed: String = arguments
            .iter()
            .map(|argument| format!(", {argument}"))
            .collect();
        Ok(format!(
            "global::PilotRuntime.Protected.Constructor<global::System.Action<{}>>(typeof({target}), new global::System.Type[] {{ {} }})(self{passed});",
            all.join(", "),
            types.join(", ")
        ))
    };
    let initializer = bound
        .statements
        .iter()
        .find_map(|statement| match &statement.kind {
            rustlyn_semantics::BoundStatementKind::ConstructorInitializer {
                constructor,
                chains_to_this,
                ..
            } => Some((*constructor, *chains_to_this)),
            _ => None,
        });
    let Some((constructor, chains_to_this)) = initializer else {
        // No `: base(...)`: the base's constructor that takes nothing.
        return match binder.base_class_of(owner) {
            None => Ok(None),
            Some(Type::Named { symbol, .. })
                if symbols.qualified_name(symbol) == "System.Object" =>
            {
                Ok(None)
            }
            Some(base) => Ok(Some((call(&base, &[], &[])?, false))),
        };
    };
    let constructor = constructor
        .ok_or_else(|| format!("{name}: the constructor it chains to was not worked out"))?;
    let written = node
        .children()
        .find(|child| {
            matches!(
                child.kind(),
                SyntaxKind::BaseConstructorInitializer | SyntaxKind::ThisConstructorInitializer
            )
        })
        .ok_or_else(|| {
            format!("{name}: a base constructor called with what its defaults fill needs a reload")
        })?;
    let detail = symbols
        .get(constructor)
        .as_method()
        .ok_or("a constructor without its detail")?;
    let target = symbols
        .get(constructor)
        .container
        .ok_or("a constructor without its type")?;
    // A base constructed from a generic one — `: base(...)` of a class
    // deriving from `Base<int>` — is called on that construction, with its
    // parameters as the construction has them.
    let target_type = match binder.base_class_of(owner) {
        Some(base @ Type::Named { symbol, .. }) if !chains_to_this && symbol == target => base,
        _ => Type::named(target),
    };
    let mut substitution = HashMap::new();
    if let Type::Named { type_arguments, .. } = &target_type {
        let parameters = symbols
            .get(target)
            .as_named_type()
            .map(|detail| detail.type_parameters.clone())
            .unwrap_or_default();
        if parameters.len() != type_arguments.len() {
            return Err(format!(
                "{name}: a constructor chained to of a generic type needs a reload"
            ));
        }
        substitution.extend(parameters.into_iter().zip(type_arguments.iter().cloned()));
    }
    if symbols
        .get(target)
        .container
        .is_some_and(|outer| generic_around(compilation, outer))
        || (substitution.is_empty() && generic_around(compilation, target))
    {
        return Err(format!(
            "{name}: a constructor of a type nested in a generic one, chained to, needs a reload"
        ));
    }
    let mut parameters = Vec::new();
    for parameter in &detail.parameters {
        let written = symbols
            .get(*parameter)
            .as_parameter()
            .ok_or("a parameter without its detail")?;
        if written.ref_kind != RefKind::None || written.is_params {
            return Err(format!(
                "{name}: a constructor chained to with `ref`, `out` or `params` needs a reload"
            ));
        }
        let declared = binder.type_of(*parameter, &mut Diagnostics::new());
        parameters.push(type_text(compilation, &declared.substitute(&substitution))?);
    }
    let arguments: Vec<SyntaxNode> = written
        .children()
        .find(|child| child.kind() == SyntaxKind::ArgumentList)
        .map(|list| {
            list.children()
                .filter(|child| child.kind() == SyntaxKind::Argument)
                .collect()
        })
        .unwrap_or_default();
    if arguments.len() != parameters.len()
        || arguments.iter().any(|argument| {
            argument
                .children()
                .any(|child| child.kind() == SyntaxKind::NameColon)
        })
    {
        return Err(format!(
            "{name}: a chained constructor not given every argument in order needs a reload"
        ));
    }
    let mut texts = Vec::new();
    for argument in &arguments {
        let edits = rewriter.edits(argument)?;
        texts.push(apply(argument, edits));
    }
    Ok(Some((
        call(&target_type, &parameters, &texts)?,
        chains_to_this,
    )))
}

/// The namespace the holder of a type added inside `outer` goes in: the
/// outer type's, or one of the patch's own where that is the global one —
/// `using static` wants a namespace block to stay inside.
fn holder_namespace(compilation: &Compilation, outer: SymbolId) -> String {
    let namespace = namespace_of(compilation, outer);
    if namespace.is_empty() {
        "__PilotGlobal".to_string()
    } else {
        namespace
    }
}

/// What turns a piece of a member's code into code a patch class can hold.
struct Rewriter<'a> {
    compilation: &'a Compilation,
    binder: &'a Binder<'a>,
    /// Whether a class is another assembly's (see `write`).
    foreign: &'a dyn Fn(SymbolId) -> bool,
    added_fields: &'a HashSet<SymbolId>,
    added_methods: &'a HashSet<SymbolId>,
    /// The getter each added property with one is read through.
    computed: &'a HashMap<SymbolId, SymbolId>,
    /// The setter each added property with one of its own is written through.
    setters: &'a HashMap<SymbolId, SymbolId>,
    /// Where each type the edit added inside another lives in the patch.
    nested: &'a HashMap<SymbolId, String>,
    tails: &'a HashMap<SymbolId, u32>,
    place: &'a dyn Fn(SymbolId) -> String,
    /// The method giving each added field its first value, where it has one.
    initializers: &'a HashMap<SymbolId, String>,
    bound: &'a BoundBody,
    /// The member the code is from, for what an error says.
    name: &'a str,
    is_static: bool,
    /// The type the member is declared in, where nested types are found.
    owner: Option<SymbolId>,
    /// The tree the code is in, for the scope of a name the binder kept
    /// nothing for.
    tree: usize,
    /// Whether the code is of a type the patch copies whole, which keeps its
    /// own `this`: only what it names of other types is rewritten.
    copied: bool,
    /// For a value a constructor gave: what each of its parameters is once
    /// it has returned, from where it kept them.
    substitute: Option<&'a HashMap<SymbolId, String>>,
}

impl Rewriter<'_> {
    /// The edits that make `root` patch code.
    fn edits(&self, root: &SyntaxNode) -> Result<Vec<(TextSpan, String)>, String> {
        // A protected member of another assembly is reached through
        // `PilotRuntime.Protected` (`protected_reach`).
        // A getter-only property set here is set through the setter the
        // editor's build opens for patches (`IncrementalOptions`).
        let Rewriter {
            compilation,
            binder,
            foreign,
            setters,
            added_fields,
            added_methods,
            computed,
            nested,
            tails,
            place,
            initializers,
            bound,
            name,
            is_static,
            owner,
            tree,
            copied,
            substitute,
        } = *self;
        let symbols = compilation.symbols();
        let target_of = |name: &SyntaxNode| -> Option<SymbolId> {
            let token = name.first_token()?;
            // What the name refers to comes first: `Check(x)` through a
            // delegate field names the field, where the call settles on the
            // delegate's `Invoke`.
            if let Some(BoundSymbol::Declared(referred)) = bound.reference_at(name.span())
                && symbols.get(referred).name == token.text()
            {
                return Some(referred);
            }
            let mut target = *bound.symbols.get(&token.span())?;
            // `new Point { ... }` names the constructor it calls: what is
            // written is the type.
            if symbols
                .get(target)
                .as_method()
                .is_some_and(|method| method.method_kind == MethodKind::Constructor)
                && let Some(ty) = symbols.get(target).container
            {
                target = ty;
            }
            Some(target)
        };
        // A receiver as the patch can repeat it: `this`, or a local or a
        // parameter, which reads the same however often it is named.
        // A receiver stays as written, evaluated once where it was, with
        // what is rewritten inside it rewritten: a mark here, filled in once
        // every edit is known.
        let receiver_text = |receiver: &SyntaxNode| -> Result<String, String> {
            let span = receiver.span();
            Ok(format!("\u{1}{}:{}\u{1}", span.start(), span.end()))
        };
        let field_access = |field: SymbolId, receiver: &str| -> Result<String, String> {
            let ty = type_text(compilation, &binder.type_of(field, &mut Diagnostics::new()))?;
            // A constant the edit added — `const`, or an enum's member — is
            // its value, which is all the loaded assembly would have had of
            // it.
            if symbols.get(field).modifiers.contains(Modifiers::CONST)
                || symbols
                    .get(field)
                    .container
                    .is_some_and(|owner| symbols.get(owner).type_kind() == Some(TypeKind::Enum))
            {
                let value = binder.constant_value(field).ok_or_else(|| {
                    format!("{name}: {} has no value", symbols.qualified_name(field))
                })?;
                return Ok(format!("(({ty}){})", literal(&value)?));
            }
            let key = symbols.qualified_name(field);
            if tails.contains_key(&field) {
                let owner = symbols
                    .get(field)
                    .container
                    .map(|owner| symbols.qualified_name(owner))
                    .unwrap_or_default();
                return Ok(format!(
                    "global::PilotTail.Access.Field<{ty}>(ref {receiver}.__pilotTail, \"{owner}\", \"{}\")",
                    symbols.get(field).name
                ));
            }
            let init = initializers
                .get(&field)
                .map(|method| format!(", {method}"))
                .unwrap_or_default();
            Ok(
                if symbols.get(field).modifiers.contains(Modifiers::STATIC) {
                    format!("global::PilotRuntime.Fields.Static<{ty}>(\"{key}\"{init})")
                } else {
                    format!("global::PilotRuntime.Fields.Of<{ty}>({receiver}, \"{key}\"{init})")
                },
            )
        };
        // After the `(` of the call `callee` is the name of: where the
        // instance a moved method now takes goes.
        let after_paren = |callee: &SyntaxNode| -> Option<(u32, bool)> {
            let invocation = callee.parent()?;
            if invocation.kind() != SyntaxKind::InvocationExpression
                || invocation.children().next()?.span() != callee.span()
            {
                return None;
            }
            let arguments = invocation
                .children()
                .find(|child| child.kind() == SyntaxKind::ArgumentList)?;
            let open = arguments.first_token()?;
            let any = arguments
                .children()
                .any(|child| child.kind() == SyntaxKind::Argument);
            Some((open.span().end(), any))
        };

        // Whether a call gives every parameter of `method` an argument, in
        // order: a delegate takes them all, by position.
        let every_argument = |callee: &SyntaxNode, method: SymbolId| -> bool {
            let Some(arguments) = callee
                .parent()
                .filter(|invocation| invocation.kind() == SyntaxKind::InvocationExpression)
                .and_then(|invocation| {
                    invocation
                        .children()
                        .find(|child| child.kind() == SyntaxKind::ArgumentList)
                })
            else {
                return false;
            };
            let given: Vec<SyntaxNode> = arguments
                .children()
                .filter(|child| child.kind() == SyntaxKind::Argument)
                .collect();
            let named = given.iter().any(|argument| {
                argument
                    .children()
                    .any(|child| child.kind() == SyntaxKind::NameColon)
            });
            !named
                && symbols
                    .get(method)
                    .as_method()
                    .is_some_and(|detail| detail.parameters.len() == given.len())
        };

        // A method the edit added, named as a delegate rather than called:
        // a lambda taking what it takes and calling the patch's.
        let method_group = |method: SymbolId, receiver: &str| -> Result<String, String> {
            let count = symbols
                .get(method)
                .as_method()
                .map_or(0, |detail| detail.parameters.len());
            let names: Vec<String> = (0..count).map(|index| format!("__a{index}")).collect();
            let mut arguments: Vec<String> = Vec::new();
            if !receiver.is_empty() && !symbols.get(method).modifiers.contains(Modifiers::STATIC) {
                arguments.push(receiver.to_string());
            }
            arguments.extend(names.iter().cloned());
            Ok(format!(
                "(({}) => {}({}))",
                names.join(", "),
                place(method),
                arguments.join(", ")
            ))
        };
        // An added field of a reference type with no first value is empty on
        // an object made before the patch — a feature's new system, which the
        // feature's patched constructor makes only for the next world. A call
        // through it whose result nothing uses is skipped there: `?.`.
        let maybe_empty = |field: SymbolId| {
            !initializers.contains_key(&field)
                && !symbols.get(field).modifiers.contains(Modifiers::CONST)
                && matches!(
                    binder.type_of(field, &mut Diagnostics::new()),
                    Type::Named { symbol, .. }
                        if matches!(
                            symbols.get(symbol).type_kind(),
                            Some(TypeKind::Class | TypeKind::Interface | TypeKind::Delegate)
                        )
                )
        };
        // Whether `receiver.M(...)` calls a method the edit added, which the
        // patch calls with the receiver as an argument instead.
        let calls_added = |receiver: &SyntaxNode| {
            receiver
                .parent()
                .and_then(|access| access.children().last())
                .and_then(|member| target_of(&member))
                .is_some_and(|method| added_methods.contains(&method))
        };
        let mut edits: Vec<(TextSpan, String)> = Vec::new();
        for inner in root.descendants() {
            match inner.kind() {
                // `a?.Added`: read through the patch's storage where `a` is
                // there, nothing where it is not.
                SyntaxKind::ConditionalAccessExpression => {
                    let (Some(owner_expression), Some(binding)) =
                        (inner.children().next(), inner.children().last())
                    else {
                        continue;
                    };
                    if binding.kind() != SyntaxKind::MemberBindingExpression {
                        continue;
                    }
                    let Some(field) = binding
                        .children()
                        .last()
                        .and_then(|name| target_of(&name))
                        .filter(|field| added_fields.contains(field) && !tails.contains_key(field))
                    else {
                        continue;
                    };
                    let mark = format!(
                        "\u{1}{}:{}\u{1}",
                        owner_expression.span().start(),
                        owner_expression.span().end()
                    );
                    let value = binder.type_of(field, &mut Diagnostics::new());
                    let reference = matches!(&value, Type::Named { symbol, .. }
                        if matches!(symbols.get(*symbol).type_kind(),
                            Some(TypeKind::Class | TypeKind::Interface | TypeKind::Delegate | TypeKind::Record)))
                        || matches!(value, Type::Array { .. });
                    let helper = if reference { "Through" } else { "ThroughValue" };
                    edits.push((
                        inner.span(),
                        format!(
                            "global::PilotRuntime.Fields.{helper}({mark}, __c => {})",
                            field_access(field, "__c")?
                        ),
                    ));
                }
                // A type copied whole is its own class: its `this` and its
                // `base` stay.
                SyntaxKind::ThisExpression | SyntaxKind::BaseExpression if copied => {}
                SyntaxKind::ThisExpression => {
                    if is_static {
                        return Err(format!("{name}: `this` in a static member"));
                    }
                    edits.push((inner.span(), "self".to_string()));
                }
                // `new T { Added = x }`: the loaded `T` has no `Added` to
                // name in an initializer. What it has is made as written, and
                // what the edit added is set on it afterwards.
                SyntaxKind::ObjectCreationExpression
                | SyntaxKind::ImplicitObjectCreationExpression => {
                    let mark =
                        |span: TextSpan| format!("\u{1}{}:{}\u{1}", span.start(), span.end());
                    // The field an initializer names, where the edit added it:
                    // the binder keeps nothing for those names, so it is
                    // found by name among the made type's added fields.
                    let made = bound.type_at(inner.span()).and_then(|ty| match ty {
                        Type::Named { symbol, .. } => Some(*symbol),
                        _ => None,
                    });
                    let initialized = |left: &SyntaxNode| -> Option<SymbolId> {
                        target_of(left)
                            .filter(|target| added_fields.contains(target))
                            .or_else(|| {
                                let name = left.first_token()?.text().to_string();
                                added_fields.iter().copied().find(|field| {
                                    symbols.get(*field).name == name
                                        && symbols.get(*field).container == made
                                })
                            })
                    };
                    // `new X(...)` through a constructor the edit added: an
                    // object made blank, given to the patch's constructor.
                    let constructor = inner
                        .children()
                        .find(|child| {
                            matches!(
                                child.kind(),
                                SyntaxKind::IdentifierName
                                    | SyntaxKind::GenericName
                                    | SyntaxKind::QualifiedName
                                    | SyntaxKind::AliasQualifiedName
                            )
                        })
                        .and_then(|ty| ty.last_token())
                        .and_then(|token| bound.symbols.get(&token.span()).copied())
                        .filter(|constructor| added_methods.contains(constructor));
                    let initializer = inner
                        .children()
                        .find(|child| child.kind() == SyntaxKind::ObjectInitializerExpression);
                    if let Some(constructor) = constructor {
                        let ty = bound.type_at(inner.span()).ok_or_else(|| {
                            format!("{name}: what `new` makes was not worked out")
                        })?;
                        let ty = type_text(compilation, ty)?;
                        let arguments: Vec<String> = inner
                            .children()
                            .find(|child| child.kind() == SyntaxKind::ArgumentList)
                            .iter()
                            .flat_map(|list| list.children())
                            .filter(|argument| argument.kind() == SyntaxKind::Argument)
                            .map(|argument| format!(", {}", mark(argument.span())))
                            .collect();
                        let by_value = symbols.get(constructor).container.is_some_and(|owner| {
                            symbols.get(owner).type_kind() == Some(TypeKind::Struct)
                        });
                        let made = if by_value {
                            format!(
                                "global::PilotRuntime.Init.With(default({ty}), (ref {ty} __o) => {}(ref __o{}))",
                                place(constructor),
                                arguments.concat()
                            )
                        } else {
                            format!(
                                "global::PilotRuntime.Init.With(global::PilotRuntime.Make.Blank<{ty}>(), (ref {ty} __o) => {}(__o{}))",
                                place(constructor),
                                arguments.concat()
                            )
                        };
                        let mut sets = Vec::new();
                        for element in initializer.iter().flat_map(|list| list.children()) {
                            let added = (element.kind() == SyntaxKind::SimpleAssignmentExpression)
                                .then(|| element.children().next())
                                .flatten()
                                .filter(|left| left.kind() == SyntaxKind::IdentifierName)
                                .and_then(|left| initialized(&left));
                            match (added, element.children().last()) {
                                (Some(field), Some(value)) => sets.push(format!(
                                    "{} = {};",
                                    field_access(field, "__v")?,
                                    mark(value.span())
                                )),
                                _ => sets.push(format!("__v.{};", mark(element.span()))),
                            }
                        }
                        let text = if sets.is_empty() {
                            made
                        } else {
                            format!(
                                "global::PilotRuntime.Init.With({made}, (ref {ty} __v) => {{ {} }})",
                                sets.join(" ")
                            )
                        };
                        edits.push((inner.span(), text));
                        continue;
                    }
                    let Some(initializer) = initializer else {
                        continue;
                    };
                    let mut kept = Vec::new();
                    let mut sets = Vec::new();
                    for element in initializer.children() {
                        let added = (element.kind() == SyntaxKind::SimpleAssignmentExpression)
                            .then(|| element.children().next())
                            .flatten()
                            .filter(|left| left.kind() == SyntaxKind::IdentifierName)
                            .and_then(|left| initialized(&left));
                        match (added, element.children().last()) {
                            (Some(field), Some(value)) => {
                                sets.push(format!(
                                    "{} = {};",
                                    field_access(field, "__v")?,
                                    mark(value.span())
                                ));
                            }
                            _ => kept.push(mark(element.span())),
                        }
                    }
                    if sets.is_empty() {
                        continue;
                    }
                    let ty = bound
                        .type_at(inner.span())
                        .ok_or_else(|| format!("{name}: what `new` makes was not worked out"))?;
                    let head = TextSpan::new(
                        inner.span().start(),
                        initializer.span().start() - inner.span().start(),
                    );
                    edits.push((
                        inner.span(),
                        format!(
                            "global::PilotRuntime.Init.With({} {{ {} }}, (ref {} __v) => {{ {} }})",
                            mark(head),
                            kept.join(", "),
                            type_text(compilation, ty)?,
                            sets.join(" ")
                        ),
                    ));
                }
                // `base.M()` from outside the class: Rustlyn calls a member
                // on `Base.Of<B>(self)` directly, as `base` does.
                SyntaxKind::BaseExpression => {
                    if is_static {
                        return Err(format!("{name}: `base` in a static member"));
                    }
                    let ty = bound
                        .type_at(inner.span())
                        .ok_or_else(|| format!("{name}: what `base` is was not worked out"))?;
                    edits.push((
                        inner.span(),
                        format!(
                            "global::PilotRuntime.Base.Of<{}>(self)",
                            type_text(compilation, ty)?
                        ),
                    ));
                }
                SyntaxKind::SimpleMemberAccessExpression => {
                    let (Some(receiver), Some(member)) =
                        (inner.children().next(), inner.children().last())
                    else {
                        continue;
                    };
                    let Some(target) = target_of(&member) else {
                        continue;
                    };
                    // `base.M()` calls the base's own: not through the
                    // override it would reach virtually.
                    let through_base = receiver.kind() == SyntaxKind::BaseExpression;
                    if let Some(reach) =
                        protected_reach(compilation, binder, foreign, target, !through_base)
                    {
                        let (callee, instance) = reach?;
                        let receiver = match (instance, through_base) {
                            (false, _) => String::new(),
                            (true, true) => "self".to_string(),
                            (true, false) => receiver_text(&receiver)?,
                        };
                        let found = symbols.get(target);
                        if found.kind == SymbolKind::Method {
                            let (at, any) = after_paren(&inner).filter(|_| every_argument(&inner, target)).ok_or_else(|| {
                                format!("{name}: {} is protected in another assembly, and not called with every argument", found.name)
                            })?;
                            edits.push((inner.span(), callee));
                            let comma = if any && instance { ", " } else { "" };
                            edits.push((TextSpan::new(at - 1, 1), format!("({receiver}{comma}")));
                        } else if written(&inner) {
                            let (expression, write) = write_of(&inner).ok_or_else(|| {
                                format!("{name}: {} is protected in another assembly, and written within an expression", found.name)
                            })?;
                            // Read and written both: what it is read on is
                            // evaluated twice, which only a name may be.
                            if !matches!(write, Write::Set(_))
                                && !matches!(
                                    inner.children().next().map(|receiver| receiver.kind()),
                                    Some(
                                        SyntaxKind::ThisExpression
                                            | SyntaxKind::BaseExpression
                                            | SyntaxKind::IdentifierName
                                    )
                                )
                            {
                                return Err(format!(
                                    "{name}: {} is protected in another assembly, and updated on an expression",
                                    found.name
                                ));
                            }
                            let (setter, value_type) =
                                protected_setter(compilation, binder, foreign, target)
                                    .ok_or("a protected member")??;
                            edits.extend(protected_write(
                                &expression,
                                &write,
                                &setter,
                                &value_type,
                                &callee,
                                &receiver,
                            ));
                        } else {
                            edits.push((inner.span(), format!("{callee}({receiver})")));
                        }
                        continue;
                    }
                    if let Some(&getter) = computed.get(&target) {
                        let shared = symbols.get(target).modifiers.contains(Modifiers::STATIC);
                        let receiver = if shared {
                            String::new()
                        } else {
                            receiver_text(&receiver)?
                        };
                        if written(&inner) {
                            let (Some(&setter), Some((expression, Write::Set(value)))) =
                                (setters.get(&target), write_of(&inner))
                            else {
                                return Err(format!(
                                    "{name}: an added property is written other than by `=` through its own setter"
                                ));
                            };
                            let comma = if receiver.is_empty() { "" } else { ", " };
                            edits.push((
                                TextSpan::new(
                                    expression.span().start(),
                                    value.span().start() - expression.span().start(),
                                ),
                                format!("{}({receiver}{comma}", place(setter)),
                            ));
                            edits.push((TextSpan::new(value.span().end(), 0), ")".to_string()));
                            continue;
                        }
                        edits.push((inner.span(), format!("{}({receiver})", place(getter))));
                    } else if added_fields.contains(&target) {
                        let receiver = receiver_text(&receiver)?;
                        edits.push((inner.span(), field_access(target, &receiver)?));
                        if maybe_empty(target) && called_and_dropped(&inner) && !calls_added(&inner)
                        {
                            edits.push((TextSpan::new(inner.span().end(), 0), "?".to_string()));
                        }
                    } else if !added_methods.contains(&target)
                        && symbols.get(target).as_method().is_some_and(|method| {
                            method.is_extension
                                && method.parameters.first().is_some_and(|first| {
                                    symbols
                                        .get(*first)
                                        .as_parameter()
                                        .is_some_and(|parameter| parameter.ref_kind == RefKind::None)
                                })
                        })
                        && receiver.kind() != SyntaxKind::PredefinedType
                        // `a?.Select(...).ToArray()`: what the call is made on
                        // starts inside `?.`, and is left as written.
                        && !receiver.first_token().is_some_and(|token| token.kind() == SyntaxKind::DotToken)
                        // `Scellecs.Morpeh.WorldExtensions.Commit(world)` is a
                        // static call already: what names the receiver last
                        // is a type, or a namespace before one.
                        && !receiver
                            .last_token()
                            .and_then(|token| bound.symbols.get(&token.span()).copied())
                            .or_else(|| target_of(&receiver))
                            .is_some_and(|found| {
                                matches!(symbols.get(found).kind, SymbolKind::NamedType | SymbolKind::Namespace)
                            })
                        && bound.type_at(receiver.span()).is_some()
                        && let Some((at, any)) = after_paren(&inner)
                        && let Some(class) = symbols.get(target).container
                    {
                        // An extension method called on its receiver is
                        // called as what it is, a static method named in
                        // full: the patch's using directives are not those
                        // of the file it was written in.
                        let type_arguments = member
                            .children()
                            .find(|child| child.kind() == SyntaxKind::TypeArgumentList)
                            .map(|list| list.text())
                            .unwrap_or_default();
                        edits.push((
                            inner.span(),
                            format!(
                                "{}.{}{type_arguments}",
                                global_name(compilation, class),
                                symbols.get(target).name
                            ),
                        ));
                        let receiver = receiver_text(&receiver)?;
                        let comma = if any { ", " } else { "" };
                        edits.push((TextSpan::new(at - 1, 1), format!("({receiver}{comma}")));
                    } else if added_methods.contains(&target) && after_paren(&inner).is_none() {
                        // `x.M` as a delegate: a lambda calling the patch's.
                        edits.push((
                            inner.span(),
                            method_group(target, &receiver_text(&receiver)?)?,
                        ));
                    } else if added_methods.contains(&target) {
                        let (at, any) = after_paren(&inner).ok_or_else(|| {
                            format!("{name}: a method the edit added is used other than by a call")
                        })?;
                        // An extension method called on a receiver takes it first.
                        let shared = symbols.get(target).modifiers.contains(Modifiers::STATIC)
                            && !symbols
                                .get(target)
                                .as_method()
                                .is_some_and(|method| method.is_extension);
                        edits.push((inner.span(), place(target)));
                        if !shared {
                            // The `(` itself is what is replaced: an edit
                            // to the first argument may start just after it.
                            // A struct's method takes the struct by reference.
                            let receiver = receiver_text(&receiver)?;
                            let comma = if any { ", " } else { "" };
                            let by = if struct_member(compilation, target) {
                                "ref "
                            } else {
                                ""
                            };
                            edits.push((
                                TextSpan::new(at - 1, 1),
                                format!("({by}{receiver}{comma}"),
                            ));
                        }
                    }
                }
                SyntaxKind::IdentifierName | SyntaxKind::GenericName => {
                    let Some(target) = target_of(&inner) else {
                        // A name the binder kept nothing for — a type
                        // argument, say — may be a type nested where the
                        // member is, which the patch's class is not in.
                        // `IconModel local;`: the type the binder gave the
                        // local is the one the name meant.
                        if let Some(declaration) = inner.parent().filter(|parent| {
                            parent.kind() == SyntaxKind::VariableDeclaration
                                && parent
                                    .children()
                                    .next()
                                    .is_some_and(|first| first.span() == inner.span())
                        }) && let Some(name) = declaration
                            .children()
                            .find(|child| child.kind() == SyntaxKind::VariableDeclarator)
                            .and_then(|declarator| declarator.first_token())
                            && let Some(local) = bound.locals.iter().find(|local| {
                                local.name == name.text()
                                    && name.span().start() <= local.span.start()
                                    && local.span.start() <= name.span().end()
                            })
                            && let Type::Named {
                                symbol: ty,
                                type_arguments,
                            } = &local.ty
                            && type_arguments.is_empty()
                            && symbols.get(*ty).kind == SymbolKind::NamedType
                            && !generic_around(compilation, *ty)
                            && inner.kind() == SyntaxKind::IdentifierName
                            && inner
                                .first_token()
                                .is_some_and(|token| token.text() == symbols.get(*ty).name)
                        {
                            let text = nested
                                .get(ty)
                                .cloned()
                                .unwrap_or_else(|| global_name(compilation, *ty));
                            edits.push((inner.span(), text));
                            continue;
                        }
                        if let Some(owner) = owner
                            && stands_alone(&inner)
                            && let Some(token) = inner.first_token()
                            && let Some(ty) = nested_named(compilation, owner, token.text())
                                .or_else(|| {
                                    // A type where only a type can stand — a
                                    // local's, a cast's — named as the scope
                                    // there names it.
                                    in_type_position(&inner)
                                        .then(|| {
                                            let arity = inner
                                                .children()
                                                .find(|child| {
                                                    child.kind() == SyntaxKind::TypeArgumentList
                                                })
                                                .map_or(0, |list| list.children().count());
                                            binder.lookup(
                                                token.text(),
                                                arity,
                                                &binder.context_at(tree, &inner),
                                            )
                                        })
                                        .flatten()
                                        .filter(|found| {
                                            symbols.get(*found).kind == SymbolKind::NamedType
                                                && !generic_around(compilation, *found)
                                        })
                                })
                        {
                            let name = nested
                                .get(&ty)
                                .cloned()
                                .unwrap_or_else(|| global_name(compilation, ty));
                            edits.push((token.span(), name));
                        }
                        continue;
                    };
                    if !stands_alone(&inner) {
                        continue;
                    }
                    let Some(token) = inner.first_token() else {
                        continue;
                    };
                    let span = token.span();
                    let found = symbols.get(target);
                    let shared = found.modifiers.contains(Modifiers::STATIC)
                        || found.modifiers.contains(Modifiers::CONST);
                    if let Some(substitute) = substitute
                        && found.kind == SymbolKind::Parameter
                    {
                        let text = substitute.get(&target).ok_or_else(|| {
                            format!(
                                "{name}: `{}` is known only while the constructor runs",
                                found.name
                            )
                        })?;
                        edits.push((span, text.clone()));
                        continue;
                    }
                    if let Some(reach) = protected_reach(compilation, binder, foreign, target, true)
                    {
                        let (callee, instance) = reach?;
                        if instance && is_static {
                            return Err(format!(
                                "{name}: a protected member used from a static one"
                            ));
                        }
                        let receiver = if instance { "self" } else { "" };
                        if found.kind == SymbolKind::Method {
                            let (at, any) = after_paren(&inner).filter(|_| every_argument(&inner, target)).ok_or_else(|| {
                                format!("{name}: {} is protected in another assembly, and not called with every argument", found.name)
                            })?;
                            edits.push((span, callee));
                            let comma = if any && instance { ", " } else { "" };
                            edits.push((TextSpan::new(at - 1, 1), format!("({receiver}{comma}")));
                        } else if written(&inner) {
                            let (expression, write) = write_of(&inner).ok_or_else(|| {
                                format!("{name}: {} is protected in another assembly, and written within an expression", found.name)
                            })?;
                            let (setter, value_type) =
                                protected_setter(compilation, binder, foreign, target)
                                    .ok_or("a protected member")??;
                            edits.extend(protected_write(
                                &expression,
                                &write,
                                &setter,
                                &value_type,
                                &callee,
                                receiver,
                            ));
                        } else {
                            edits.push((span, format!("{callee}({receiver})")));
                        }
                        continue;
                    }
                    if let Some(&getter) = computed.get(&target) {
                        let receiver = if shared { "" } else { "self" };
                        if written(&inner) {
                            let (Some(&setter), Some((expression, Write::Set(value)))) =
                                (setters.get(&target), write_of(&inner))
                            else {
                                return Err(format!(
                                    "{name}: an added property is written other than by `=` through its own setter"
                                ));
                            };
                            let comma = if receiver.is_empty() { "" } else { ", " };
                            edits.push((
                                TextSpan::new(
                                    expression.span().start(),
                                    value.span().start() - expression.span().start(),
                                ),
                                format!("{}({receiver}{comma}", place(setter)),
                            ));
                            edits.push((TextSpan::new(value.span().end(), 0), ")".to_string()));
                            continue;
                        }
                        edits.push((span, format!("{}({receiver})", place(getter))));
                        continue;
                    }
                    if added_fields.contains(&target) {
                        if !shared && is_static {
                            continue;
                        }
                        edits.push((span, field_access(target, "self")?));
                        if maybe_empty(target) && called_and_dropped(&inner) && !calls_added(&inner)
                        {
                            edits.push((TextSpan::new(span.end(), 0), "?".to_string()));
                        }
                        continue;
                    }
                    if added_methods.contains(&target) && after_paren(&inner).is_none() {
                        let receiver = if shared {
                            String::new()
                        } else {
                            "self".to_string()
                        };
                        edits.push((span, method_group(target, &receiver)?));
                        continue;
                    }
                    if added_methods.contains(&target) {
                        let (at, any) = after_paren(&inner).ok_or_else(|| {
                            format!("{name}: a method the edit added is used other than by a call")
                        })?;
                        edits.push((span, place(target)));
                        if !shared {
                            let comma = if any { ", " } else { "" };
                            let by = if struct_member(compilation, target) {
                                "ref "
                            } else {
                                ""
                            };
                            edits.push((TextSpan::new(at - 1, 1), format!("({by}self{comma}")));
                        }
                        continue;
                    }
                    // `World.Default` where `World` is both a member and its
                    // type (§12.8.7.2): a static member after it means the
                    // type.
                    if matches!(found.kind, SymbolKind::Field | SymbolKind::Property)
                        && let Some(access) = inner.parent().filter(|parent| {
                            parent.kind() == SyntaxKind::SimpleMemberAccessExpression
                                && parent
                                    .children()
                                    .next()
                                    .is_some_and(|first| first.span() == inner.span())
                        })
                        && let Some(member) = access
                            .children()
                            .last()
                            .and_then(|member| target_of(&member))
                        && !symbols
                            .get(member)
                            .as_method()
                            .is_some_and(|method| method.is_extension)
                        && (symbols.get(member).modifiers.contains(Modifiers::STATIC)
                            || symbols.get(member).modifiers.contains(Modifiers::CONST)
                            || symbols.get(member).kind == SymbolKind::NamedType)
                        && let Some(Type::Named { symbol: ty, .. }) = binder
                            .type_of(target, &mut Diagnostics::new())
                            .clone()
                            .into()
                        && symbols.get(ty).name == found.name
                    {
                        edits.push((span, global_name(compilation, ty)));
                        continue;
                    }
                    let container = found
                        .container
                        .filter(|container| symbols.get(*container).kind == SymbolKind::NamedType);
                    match (found.kind, container) {
                        (
                            SymbolKind::Field
                            | SymbolKind::Property
                            | SymbolKind::Method
                            | SymbolKind::Event,
                            Some(container),
                        ) if found.name == token.text() => {
                            // `action()` on a delegate the binder settles on
                            // its `Invoke`: a member, but not of this type,
                            // and not what is written.
                            if copied {
                                continue;
                            }
                            let prefix = if shared {
                                format!("{}.", global_name(compilation, container))
                            } else {
                                if is_static || copied {
                                    continue;
                                }
                                "self.".to_string()
                            };
                            edits.push((TextSpan::new(span.start(), 0), prefix));
                        }
                        // A type is named from the global namespace: the patch
                        // gathers the using directives of many files, under
                        // which a short name may mean another type.
                        (SymbolKind::NamedType, _)
                            if token.text() != "var"
                                && token.text() != "dynamic"
                                && !found.name.starts_with('<')
                                && !generic_outside(compilation, target) =>
                        {
                            let name = nested
                                .get(&target)
                                .cloned()
                                .unwrap_or_else(|| global_name(compilation, target));
                            edits.push((span, name));
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        let text = root.text();
        let start = root.span().start();
        let resolved = edits
            .iter()
            .map(|(span, replacement)| (*span, fill_receivers(replacement, &text, start, &edits)))
            .collect();
        Ok(resolved)
    }
}

/// `replacement` with each receiver mark replaced by the receiver's text,
/// rewritten by the edits inside it.
fn fill_receivers(
    replacement: &str,
    text: &str,
    start: u32,
    edits: &[(TextSpan, String)],
) -> String {
    let mut out = String::new();
    let mut rest = replacement;
    while let Some(open) = rest.find('\u{1}') {
        out.push_str(&rest[..open]);
        let after = &rest[open + 1..];
        let close = after.find('\u{1}').expect("a receiver mark is closed");
        let (from, to) = after[..close]
            .split_once(':')
            .expect("a receiver mark holds a span");
        let span = TextSpan::new(
            from.parse().expect("a span start"),
            to.parse::<u32>().expect("a span end") - from.parse::<u32>().expect("a span start"),
        );
        let inside: Vec<(TextSpan, String)> = edits
            .iter()
            .filter(|(edit, _)| span.start() <= edit.start() && edit.end() <= span.end())
            .cloned()
            .collect();
        let piece = apply_text(text, start, span, inside.clone());
        out.push_str(&fill_receivers(&piece, text, start, &inside));
        rest = &after[close + 1..];
    }
    out.push_str(rest);
    out
}

/// A constructor's parameters as what it kept of each — a member it
/// assigned the parameter to — which stands for the parameter once the
/// constructor has returned.
fn kept_parameters(
    compilation: &Compilation,
    declaration: &SyntaxNode,
    bound: &BoundBody,
    added_fields: &HashSet<SymbolId>,
    constructor: bool,
) -> HashMap<SymbolId, String> {
    let symbols = compilation.symbols();
    let mut kept: HashMap<SymbolId, String> = HashMap::new();
    if constructor {
        for statement in declaration
            .children()
            .find(|child| child.kind() == SyntaxKind::Block)
            .into_iter()
            .flat_map(|block| block.children())
        {
            let Some(assignment) = statement
                .children()
                .find(|child| child.kind() == SyntaxKind::SimpleAssignmentExpression)
            else {
                continue;
            };
            let (Some(left), Some(right)) =
                (assignment.children().next(), assignment.children().last())
            else {
                continue;
            };
            let token_target = |node: &SyntaxNode| {
                node.first_token()
                    .and_then(|token| bound.symbols.get(&token.span()).copied())
            };
            let member = match left.kind() {
                SyntaxKind::IdentifierName => token_target(&left),
                SyntaxKind::SimpleMemberAccessExpression => left
                    .children()
                    .last()
                    .and_then(|member| token_target(&member)),
                _ => None,
            };
            if right.kind() == SyntaxKind::IdentifierName
                && let (Some(member), Some(parameter)) = (member, token_target(&right))
                && symbols.get(parameter).kind == SymbolKind::Parameter
                && matches!(
                    symbols.get(member).kind,
                    SymbolKind::Field | SymbolKind::Property
                )
                && !added_fields.contains(&member)
            {
                kept.insert(parameter, format!("self.{}", symbols.get(member).name));
            }
        }
    }
    kept
}

/// Whether `value` names a parameter of the constructor it is in that
/// nothing kept: one whose value is gone.
fn names_a_lost_parameter(
    value: &SyntaxNode,
    bound: &BoundBody,
    symbols: &rustlyn_semantics::Symbols,
    kept: &HashMap<SymbolId, String>,
) -> bool {
    value.descendants().any(|name| {
        name.kind() == SyntaxKind::IdentifierName
            && name
                .first_token()
                .and_then(|token| bound.symbols.get(&token.span()).copied())
                .is_some_and(|target| {
                    symbols.get(target).kind == SymbolKind::Parameter && !kept.contains_key(&target)
                })
    })
}

/// Whether a constructor can be patched: one that chains to nothing a patch
/// could not do itself — a struct's, or a class's whose base is `object`,
/// either without `: this(...)` or `: base(...)`. A class's field
/// initializers run in its constructors, so the patch runs them first.
pub(crate) fn patchable_constructor(compilation: &Compilation, constructor: SymbolId) -> bool {
    let symbols = compilation.symbols();
    let Some(owner) = symbols.get(constructor).container else {
        return false;
    };
    let chains = compilation
        .declaration_node(constructor)
        .is_some_and(|node| {
            node.children().any(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::BaseConstructorInitializer | SyntaxKind::ThisConstructorInitializer
                )
            })
        });
    if generic_around(compilation, owner) {
        return false;
    }
    match symbols.get(owner).type_kind() {
        Some(TypeKind::Struct) => !chains,
        // A class's chains to its base's or another of its own: the patch
        // calls that one through `PilotRuntime.Protected.Constructor`.
        Some(TypeKind::Class) => true,
        _ => false,
    }
}

/// Whether a property is storage alone — `{ get; set; }`, with or without
/// an initializer — rather than code of its own.
pub(crate) fn is_stored(compilation: &Compilation, property: SymbolId) -> bool {
    let symbols = compilation.symbols();
    let Some(detail) = symbols.get(property).as_property() else {
        return false;
    };
    detail.getter.is_none()
        && detail.setter.is_none()
        && !detail.is_indexer
        && compilation.declaration_node(property).is_some_and(|node| {
            node.children()
                .all(|child| child.kind() != SyntaxKind::ArrowExpressionClause)
        })
}

/// The type a patched method belongs to, where it is one a patch can stand
/// in for: not generic, nor inside a generic type.
/// A generic method is patched only where it is new: nothing jumps to it,
/// and a call to it is written as a call to the patch's.
fn owner_of(compilation: &Compilation, id: SymbolId, added: bool) -> Result<SymbolId, String> {
    let symbols = compilation.symbols();
    let symbol = symbols.get(id);
    let name = symbols.qualified_name(id);
    // A property that is its own getter, or an accessor declared under its
    // property: either belongs to the type the property does.
    let in_type = |container: Option<SymbolId>| {
        let mut container = container?;
        if matches!(
            symbols.get(container).kind,
            SymbolKind::Property | SymbolKind::Event
        ) {
            container = symbols.get(container).container?;
        }
        (symbols.get(container).kind == SymbolKind::NamedType).then_some(container)
    };
    if symbol.kind == SymbolKind::Property {
        let owner = in_type(Some(id)).ok_or_else(|| format!("{name} is not a member of a type"))?;
        if generic_around(compilation, owner) {
            return Err(format!("{name}: a member of a generic type needs a reload"));
        }
        return Ok(owner);
    }
    let detail = symbol
        .as_method()
        .ok_or_else(|| format!("{name} is not a method"))?;
    // A struct's constructor chains to nothing: all it does is in its body,
    // and the patch can do it from outside. A class's calls its base's.
    let struct_constructor =
        detail.method_kind == MethodKind::Constructor && patchable_constructor(compilation, id);
    if !struct_constructor
        && !matches!(
            detail.method_kind,
            MethodKind::Ordinary
                | MethodKind::PropertyGet
                | MethodKind::PropertySet
                | MethodKind::Operator
                | MethodKind::Conversion
        )
    {
        return Err(format!("{name}: a {:?} needs a reload", detail.method_kind));
    }
    if !detail.type_parameters.is_empty() && !added {
        return Err(format!(
            "{name}: a change to a generic method needs a reload"
        ));
    }
    let owner =
        in_type(symbol.container).ok_or_else(|| format!("{name} is not a member of a type"))?;
    if generic_around(compilation, owner) {
        return Err(format!("{name}: a member of a generic type needs a reload"));
    }
    Ok(owner)
}

/// The using directives of a file, wherever they stand in it.
fn collect_usings(compilation: &Compilation, tree: usize, usings: &mut Vec<String>) {
    if let Some(root) = compilation.trees().get(tree).map(|tree| tree.root()) {
        for directive in root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::UsingDirective)
        {
            let text = directive.text().trim().to_string();
            if !usings.contains(&text) {
                usings.push(text);
            }
        }
    }
}

/// A type's head with what kept it to its outer type opened to the
/// assembly: `private` and `protected` become `internal`.
fn opened_head(head: &str) -> String {
    head.replace("private protected", "internal")
        .replace("protected internal", "internal")
        .replace("private ", "internal ")
        .replace("protected ", "internal ")
}

/// A type's declaration with what kept it to its outer type opened to the
/// assembly: `private` and `protected` become `internal`.
#[allow(dead_code)]
fn opened(node: &SyntaxNode) -> String {
    let text = node.text();
    let start = node.span().start() as usize;
    // Only the modifiers, which stand before the keyword that says what the
    // type is.
    let keyword = node
        .child_tokens()
        .find(|token| {
            matches!(
                token.kind(),
                SyntaxKind::ClassKeyword
                    | SyntaxKind::StructKeyword
                    | SyntaxKind::InterfaceKeyword
                    | SyntaxKind::EnumKeyword
                    | SyntaxKind::RecordKeyword
                    | SyntaxKind::DelegateKeyword
            )
        })
        .map_or(0, |token| token.span().start() as usize - start);
    let head = text[..keyword]
        .replace("private protected", "internal")
        .replace("protected internal", "internal")
        .replace("private ", "internal ")
        .replace("protected ", "internal ");
    format!("{head}{}", &text[keyword..])
}

/// A constant as C# writes it.
fn literal(value: &rustlyn_semantics::ConstantValue) -> Result<String, String> {
    use rustlyn_semantics::ConstantValue as Value;
    Ok(match value {
        Value::Null => "null".to_string(),
        Value::Boolean(value) => value.to_string(),
        Value::Char(value) => format!("'\\u{:04x}'", *value as u32),
        Value::Int32(value) => format!("({value})"),
        Value::UInt32(value) => format!("{value}u"),
        Value::Int64(value) => format!("({value}L)"),
        Value::UInt64(value) => format!("{value}ul"),
        Value::Single(value) if value.is_finite() => format!("({value:?}f)"),
        Value::Double(value) if value.is_finite() => format!("({value:?}d)"),
        Value::String(value) => {
            let mut text = String::from("\"");
            for character in value.chars() {
                match character {
                    '"' => text.push_str("\\\""),
                    '\\' => text.push_str("\\\\"),
                    character if (character as u32) < 0x20 || character as u32 > 0x7e => {
                        let mut units = [0u16; 2];
                        for unit in character.encode_utf16(&mut units) {
                            text.push_str(&format!("\\u{unit:04x}"));
                        }
                    }
                    character => text.push(character),
                }
            }
            text.push('"');
            text
        }
        other => return Err(format!("a constant {other:?} cannot be written")),
    })
}

/// A type named `name` nested in `owner` or in a type around it — not
/// generic, since its name alone would not say which.
fn nested_named(compilation: &Compilation, owner: SymbolId, name: &str) -> Option<SymbolId> {
    let symbols = compilation.symbols();
    let mut current = Some(owner);
    while let Some(ty) = current {
        if symbols.get(ty).kind != SymbolKind::NamedType {
            return None;
        }
        if let Some(&found) = symbols.lookup(ty, name).iter().find(|&&found| {
            symbols.get(found).kind == SymbolKind::NamedType
                && symbols
                    .get(found)
                    .as_named_type()
                    .is_some_and(|detail| detail.type_parameters.is_empty())
        }) {
            return Some(found);
        }
        current = symbols.get(ty).container;
    }
    None
}

/// Whether a name stands where only a type can: the type of a local, a
/// parameter, a cast, `new`, `typeof`, `default`, a type argument, an array
/// or a nullable, a pattern's or a `foreach`'s.
fn in_type_position(name: &SyntaxNode) -> bool {
    let Some(parent) = name.parent() else {
        return false;
    };
    let first = parent
        .children()
        .next()
        .is_some_and(|child| child.span() == name.span());
    match parent.kind() {
        SyntaxKind::TypeArgumentList
        | SyntaxKind::ArrayType
        | SyntaxKind::NullableType
        | SyntaxKind::TypeOfExpression
        | SyntaxKind::DefaultExpression
        | SyntaxKind::ObjectCreationExpression
        | SyntaxKind::ArrayCreationExpression => true,
        SyntaxKind::VariableDeclaration
        | SyntaxKind::Parameter
        | SyntaxKind::CastExpression
        | SyntaxKind::DeclarationExpression
        | SyntaxKind::DeclarationPattern
        | SyntaxKind::ForEachStatement
        | SyntaxKind::LocalFunctionStatement => {
            first || parent.kind() == SyntaxKind::CastExpression
        }
        _ => false,
    }
}

/// Whether `receiver` is what a member is called on in a statement of its
/// own: `receiver.M(...);`.
fn called_and_dropped(receiver: &SyntaxNode) -> bool {
    let Some(access) = receiver.parent() else {
        return false;
    };
    access.kind() == SyntaxKind::SimpleMemberAccessExpression
        && access
            .children()
            .next()
            .is_some_and(|first| first.span() == receiver.span())
        && access.parent().is_some_and(|call| {
            call.kind() == SyntaxKind::InvocationExpression
                && call
                    .parent()
                    .is_some_and(|statement| statement.kind() == SyntaxKind::ExpressionStatement)
        })
}

/// Whether an expression is written to: assigned, incremented, or passed by
/// reference.
fn written(expression: &SyntaxNode) -> bool {
    let Some(parent) = expression.parent() else {
        return false;
    };
    let first = parent
        .children()
        .next()
        .is_some_and(|child| child.span() == expression.span());
    match parent.kind() {
        SyntaxKind::SimpleAssignmentExpression
        | SyntaxKind::AddAssignmentExpression
        | SyntaxKind::SubtractAssignmentExpression
        | SyntaxKind::MultiplyAssignmentExpression
        | SyntaxKind::DivideAssignmentExpression
        | SyntaxKind::ModuloAssignmentExpression
        | SyntaxKind::AndAssignmentExpression
        | SyntaxKind::OrAssignmentExpression
        | SyntaxKind::ExclusiveOrAssignmentExpression
        | SyntaxKind::LeftShiftAssignmentExpression
        | SyntaxKind::RightShiftAssignmentExpression
        | SyntaxKind::CoalesceAssignmentExpression => first,
        SyntaxKind::PreIncrementExpression
        | SyntaxKind::PreDecrementExpression
        | SyntaxKind::PostIncrementExpression
        | SyntaxKind::PostDecrementExpression => true,
        SyntaxKind::Argument => parent.child_tokens().any(|token| {
            matches!(
                token.kind(),
                SyntaxKind::RefKeyword | SyntaxKind::OutKeyword
            )
        }),
        _ => false,
    }
}

/// Whether a name stands on its own rather than after a receiver, as the
/// name of a member being initialized or matched, or as a qualified part.
fn stands_alone(name: &SyntaxNode) -> bool {
    let Some(parent) = name.parent() else {
        return true;
    };
    let first = parent
        .children()
        .next()
        .is_some_and(|child| child.span() == name.span());
    match parent.kind() {
        SyntaxKind::SimpleMemberAccessExpression
        | SyntaxKind::PointerMemberAccessExpression
        | SyntaxKind::QualifiedName
        | SyntaxKind::AliasQualifiedName => first,
        SyntaxKind::MemberBindingExpression
        | SyntaxKind::NameColon
        | SyntaxKind::NameEquals
        | SyntaxKind::ExpressionColon => false,
        SyntaxKind::SimpleAssignmentExpression if first => !parent.parent().is_some_and(|holder| {
            matches!(
                holder.kind(),
                SyntaxKind::ObjectInitializerExpression | SyntaxKind::WithInitializerExpression
            )
        }),
        _ => true,
    }
}

/// The body's text with each edit made: a span replaced, or text put in
/// front of a position where the span is empty.
fn apply(body: &SyntaxNode, edits: Vec<(TextSpan, String)>) -> String {
    apply_text(&body.text(), body.span().start(), body.span(), edits)
}

/// The part `span` of `text` — which starts at `start` — with each edit in
/// it made.
fn apply_text(
    whole: &str,
    start: u32,
    span: TextSpan,
    mut edits: Vec<(TextSpan, String)>,
) -> String {
    let text = &whole[(span.start() - start) as usize..(span.end() - start) as usize];
    let start = span.start();
    // Outer edits first: an inner one inside a span already replaced is
    // dropped; insertions at one place keep the order they were made in.
    edits.sort_by_key(|(span, _)| (span.start(), std::cmp::Reverse(span.length())));
    let mut out = String::with_capacity(text.len() + edits.len() * 8);
    let mut at = 0usize;
    for (span, replacement) in edits {
        let from = (span.start() - start) as usize;
        if from < at {
            continue;
        }
        out.push_str(&text[at..from]);
        out.push_str(&replacement);
        at = from + span.length() as usize;
    }
    out.push_str(&text[at..]);
    out
}

/// Whether a member is a struct's: its patch method takes the struct by
/// reference.
fn struct_member(compilation: &Compilation, member: SymbolId) -> bool {
    let symbols = compilation.symbols();
    symbols
        .get(member)
        .container
        .is_some_and(|owner| symbols.get(owner).type_kind() == Some(TypeKind::Struct))
}

/// Whether a type is nested in a generic one: its full name would need the
/// outer type's arguments, which the name written does not hold. A generic
/// type itself is named fully all the same — its own arguments follow the
/// name in the text.
fn generic_outside(compilation: &Compilation, ty: SymbolId) -> bool {
    let symbols = compilation.symbols();
    symbols
        .get(ty)
        .container
        .filter(|container| symbols.get(*container).kind == SymbolKind::NamedType)
        .is_some_and(|container| generic_around(compilation, container))
}

pub(crate) fn generic_around(compilation: &Compilation, ty: SymbolId) -> bool {
    let symbols = compilation.symbols();
    let mut current = Some(ty);
    while let Some(id) = current {
        let symbol = symbols.get(id);
        if symbol
            .as_named_type()
            .is_some_and(|detail| !detail.type_parameters.is_empty())
        {
            return true;
        }
        current = symbol
            .container
            .filter(|container| symbols.get(*container).kind == SymbolKind::NamedType);
    }
    false
}

/// The names from the outermost type in to this one.
fn type_path(compilation: &Compilation, ty: SymbolId) -> Vec<String> {
    let symbols = compilation.symbols();
    let mut path = Vec::new();
    let mut current = Some(ty);
    while let Some(id) = current {
        let symbol = symbols.get(id);
        if symbol.kind != SymbolKind::NamedType {
            break;
        }
        path.push(symbol.name.clone());
        current = symbol.container;
    }
    path.reverse();
    path
}

fn namespace_of(compilation: &Compilation, ty: SymbolId) -> String {
    let symbols = compilation.symbols();
    let mut current = symbols.get(ty).container;
    while let Some(id) = current {
        if symbols.get(id).kind != SymbolKind::NamedType {
            break;
        }
        current = symbols.get(id).container;
    }
    let mut parts = Vec::new();
    while let Some(id) = current {
        let symbol = symbols.get(id);
        if !symbol.name.is_empty() {
            parts.push(symbol.name.clone());
        }
        current = symbol.container;
    }
    parts.reverse();
    parts.join(".")
}

/// `global::Namespace.Outer.Inner`, as C# names a type from anywhere.
/// How a patch writes a `protected` property or field of a class from
/// another assembly: the delegate `PilotRuntime.Protected` makes, called
/// with the receiver (where there is one) and the value. `None` where the
/// member is no such; an error where it cannot be written so.
fn protected_setter(
    compilation: &Compilation,
    binder: &Binder,
    foreign: &dyn Fn(SymbolId) -> bool,
    target: SymbolId,
) -> Option<Result<(String, String), String>> {
    let symbols = compilation.symbols();
    let found = symbols.get(target);
    // What `protected_reach` reaches, it can tell apart.
    let reached = protected_reach(compilation, binder, foreign, target, true)?;
    Some((|| {
        reached?;
        let owner = found.container.ok_or("a member without its class")?;
        let owner_text = global_name(compilation, owner);
        let instance = !found.modifiers.contains(Modifiers::STATIC);
        let value = type_text(
            compilation,
            &binder.type_of(target, &mut Diagnostics::new()),
        )?;
        let delegate = if instance {
            format!("global::System.Action<{owner_text}, {value}>")
        } else {
            format!("global::System.Action<{value}>")
        };
        match found.kind {
            SymbolKind::Property => {
                // From metadata a property has its setter; from source, the
                // `set` it declares.
                if found
                    .as_property()
                    .is_none_or(|detail| detail.setter.is_none() && !detail.has_set)
                {
                    return Err(format!(
                        "{}: a protected property of another assembly without a setter is written",
                        found.name
                    ));
                }
                Ok((
                    format!(
                        "global::PilotRuntime.Protected.Call<{delegate}>(typeof({owner_text}), \"set_{}\", new global::System.Type[] {{ typeof({value}) }}, true)",
                        found.name
                    ),
                    value,
                ))
            }
            _ => Ok((
                format!(
                    "global::PilotRuntime.Protected.SetField<{delegate}>(typeof({owner_text}), \"{}\")",
                    found.name
                ),
                value,
            )),
        }
    })())
}

/// How a member is written by a statement of its own — `x = v;`, `x += v;`,
/// `x++;` — which a call can stand for, nothing reading the value.
enum Write {
    /// `x = v`: the value.
    Set(SyntaxNode),
    /// `x op= v`: the operator and the value.
    Compound(&'static str, SyntaxNode),
    /// `x++`, `--x`: `+` or `-`.
    Step(&'static str),
}

/// The write `target` is the target of, and the expression that is it.
fn write_of(target: &SyntaxNode) -> Option<(SyntaxNode, Write)> {
    let expression = target.parent()?;
    if expression.parent()?.kind() != SyntaxKind::ExpressionStatement {
        return None;
    }
    let operator = match expression.kind() {
        SyntaxKind::PreIncrementExpression | SyntaxKind::PostIncrementExpression => {
            return Some((expression.clone(), Write::Step("+")));
        }
        SyntaxKind::PreDecrementExpression | SyntaxKind::PostDecrementExpression => {
            return Some((expression.clone(), Write::Step("-")));
        }
        SyntaxKind::SimpleAssignmentExpression => None,
        SyntaxKind::AddAssignmentExpression => Some("+"),
        SyntaxKind::SubtractAssignmentExpression => Some("-"),
        SyntaxKind::MultiplyAssignmentExpression => Some("*"),
        SyntaxKind::DivideAssignmentExpression => Some("/"),
        SyntaxKind::ModuloAssignmentExpression => Some("%"),
        SyntaxKind::AndAssignmentExpression => Some("&"),
        SyntaxKind::OrAssignmentExpression => Some("|"),
        SyntaxKind::ExclusiveOrAssignmentExpression => Some("^"),
        SyntaxKind::LeftShiftAssignmentExpression => Some("<<"),
        SyntaxKind::RightShiftAssignmentExpression => Some(">>"),
        _ => return None,
    };
    if expression.children().next()?.span() != target.span() {
        return None;
    }
    let value = expression.children().last()?;
    Some((
        expression.clone(),
        operator.map_or(Write::Set(value.clone()), |operator| {
            Write::Compound(operator, value)
        }),
    ))
}

/// The edits that make `expression`, a write of a protected member, a call
/// of its setter: `read` reads the member, `receiver` is what it is read on.
fn protected_write(
    expression: &SyntaxNode,
    write: &Write,
    setter: &str,
    value_type: &str,
    read: &str,
    receiver: &str,
) -> Vec<(TextSpan, String)> {
    let comma = if receiver.is_empty() { "" } else { ", " };
    let head = |value: &SyntaxNode| {
        TextSpan::new(
            expression.span().start(),
            value.span().start() - expression.span().start(),
        )
    };
    match write {
        Write::Set(value) => vec![
            (head(value), format!("{setter}({receiver}{comma}")),
            (TextSpan::new(value.span().end(), 0), ")".to_string()),
        ],
        // C#'s compound assignment converts back to the member's type.
        Write::Compound(operator, value) => vec![
            (
                head(value),
                format!("{setter}({receiver}{comma}({value_type})({read}({receiver}) {operator} ("),
            ),
            (TextSpan::new(value.span().end(), 0), ")))".to_string()),
        ],
        Write::Step(operator) => vec![(
            expression.span(),
            format!("{setter}({receiver}{comma}({value_type})({read}({receiver}) {operator} 1))"),
        )],
    }
}

/// How a patch reaches a member of a class from another assembly that only
/// that class's own code may reach — `protected`: through a delegate
/// `PilotRuntime.Protected` makes, which the runtime lets past the access
/// check, `call`ing rather than `callvirt`ing it for `base.M()`. The text is
/// the delegate: a method's is called with the receiver first, a property's
/// or a field's with the receiver alone to read it. `None` where the member
/// is no such; an error where no delegate carries it.
fn protected_reach(
    compilation: &Compilation,
    binder: &Binder,
    foreign: &dyn Fn(SymbolId) -> bool,
    target: SymbolId,
    virtual_call: bool,
) -> Option<Result<(String, bool), String>> {
    use rustlyn_semantics::Accessibility;
    let symbols = compilation.symbols();
    let found = symbols.get(target);
    if !matches!(
        found.accessibility,
        Accessibility::Protected
            | Accessibility::ProtectedOrInternal
            | Accessibility::ProtectedAndInternal
    ) || !matches!(
        found.kind,
        SymbolKind::Method | SymbolKind::Property | SymbolKind::Field
    ) {
        return None;
    }
    let owner = found.container?;
    if !foreign(owner) {
        return None;
    }
    let refused = |why: &str| {
        Err(format!(
            "{}: {} is protected in {}, of another assembly, and {why}",
            symbols.qualified_name(target),
            found.name,
            symbols.qualified_name(owner)
        ))
    };
    if symbols
        .get(owner)
        .as_named_type()
        .is_none_or(|detail| !detail.type_parameters.is_empty())
    {
        return Some(refused("its class is generic"));
    }
    let owner_text = global_name(compilation, owner);
    let instance = !found.modifiers.contains(Modifiers::STATIC);
    let ty = binder.type_of(target, &mut Diagnostics::new());
    let delegate = |parameters: &[String], returns: Option<&str>| -> Option<String> {
        let mut all: Vec<String> = Vec::new();
        if instance {
            all.push(owner_text.clone());
        }
        all.extend(parameters.iter().cloned());
        match returns {
            None if all.is_empty() => Some("global::System.Action".to_string()),
            None if all.len() <= 16 => Some(format!("global::System.Action<{}>", all.join(", "))),
            Some(returned) if all.len() < 16 => {
                all.push(returned.to_string());
                Some(format!("global::System.Func<{}>", all.join(", ")))
            }
            _ => None,
        }
    };
    Some((|| match found.kind {
        SymbolKind::Method => {
            let detail = found.as_method().ok_or("a method without its detail")?;
            if !detail.type_parameters.is_empty() {
                return refused("it is generic");
            }
            let mut parameters = Vec::new();
            for parameter in &detail.parameters {
                let written = symbols
                    .get(*parameter)
                    .as_parameter()
                    .ok_or("a parameter without its detail")?;
                if written.ref_kind != RefKind::None || written.is_params {
                    return refused("it takes a `ref`, `out` or `params` parameter");
                }
                parameters.push(type_text(
                    compilation,
                    &binder.type_of(*parameter, &mut Diagnostics::new()),
                )?);
            }
            let returned = match &ty {
                Type::Void => None,
                Type::ByRef(_) => return refused("it returns a reference"),
                other => Some(type_text(compilation, other)?),
            };
            let delegate = delegate(&parameters, returned.as_deref())
                .ok_or_else(|| format!("{}: too many parameters for a delegate", found.name))?;
            let types: Vec<String> = parameters
                .iter()
                .map(|ty| format!("typeof({ty})"))
                .collect();
            Ok((
                format!(
                    "global::PilotRuntime.Protected.Call<{delegate}>(typeof({owner_text}), \"{}\", new global::System.Type[] {{ {} }}, {virtual_call})",
                    found.name,
                    types.join(", ")
                ),
                instance,
            ))
        }
        SymbolKind::Property => {
            let detail = found.as_property().ok_or("a property without its detail")?;
            if detail.is_indexer {
                return refused("it is an indexer");
            }
            let returned = type_text(compilation, &ty)?;
            let delegate = delegate(&[], Some(&returned)).ok_or("a delegate for a property")?;
            Ok((
                format!(
                    "global::PilotRuntime.Protected.Call<{delegate}>(typeof({owner_text}), \"get_{}\", new global::System.Type[0], {virtual_call})",
                    found.name
                ),
                instance,
            ))
        }
        _ => {
            let returned = type_text(compilation, &ty)?;
            let delegate = delegate(&[], Some(&returned)).ok_or("a delegate for a field")?;
            Ok((
                format!(
                    "global::PilotRuntime.Protected.Field<{delegate}>(typeof({owner_text}), \"{}\")",
                    found.name
                ),
                instance,
            ))
        }
    })())
}

fn global_name(compilation: &Compilation, ty: SymbolId) -> String {
    let namespace = namespace_of(compilation, ty);
    let path = type_path(compilation, ty).join(".");
    if namespace.is_empty() {
        format!("global::{path}")
    } else {
        format!("global::{namespace}.{path}")
    }
}

/// A type as C# writes it from anywhere.
fn type_text(compilation: &Compilation, ty: &Type) -> Result<String, String> {
    let symbols = compilation.symbols();
    Ok(match ty {
        Type::Void => "void".to_string(),
        Type::Dynamic => "dynamic".to_string(),
        Type::TypeParameter(id) => symbols.get(*id).name.clone(),
        Type::Named {
            symbol,
            type_arguments,
        } => {
            let mut text = global_name(compilation, *symbol);
            if !type_arguments.is_empty() {
                let arguments = type_arguments
                    .iter()
                    .map(|argument| type_text(compilation, argument))
                    .collect::<Result<Vec<_>, _>>()?;
                text.push_str(&format!("<{}>", arguments.join(", ")));
            }
            text
        }
        Type::Array { element, rank } => format!(
            "{}[{}]",
            type_text(compilation, element)?,
            ",".repeat(rank.saturating_sub(1))
        ),
        Type::Pointer(inner) => format!("{}*", type_text(compilation, inner)?),
        Type::ByRef(inner) => type_text(compilation, inner)?,
        Type::Tuple(elements) => {
            let parts = elements
                .iter()
                .map(|element| type_text(compilation, &element.ty))
                .collect::<Result<Vec<_>, _>>()?;
            format!("({})", parts.join(", "))
        }
        other => return Err(format!("a parameter of type {other:?} cannot be written")),
    })
}

/// What reflection's `Type.Name` says of a parameter's type.
fn reflection_name(compilation: &Compilation, ty: &Type) -> String {
    let symbols = compilation.symbols();
    match ty {
        Type::Named { symbol, .. } => symbols.get(*symbol).metadata_name(),
        Type::Array { element, rank } => format!(
            "{}[{}]",
            reflection_name(compilation, element),
            ",".repeat(rank.saturating_sub(1))
        ),
        Type::Pointer(inner) => format!("{}*", reflection_name(compilation, inner)),
        Type::ByRef(inner) => reflection_name(compilation, inner),
        Type::TypeParameter(id) => symbols.get(*id).name.clone(),
        Type::Tuple(elements) => format!("ValueTuple`{}", elements.len()),
        _ => "Object".to_string(),
    }
}
