//! Generate overrides: overrides of the virtual and abstract members a type
//! inherits and does not override yet.
//!
//! Roslyn's `GenerateOverrides` refactoring, which Visual Studio drives
//! through a dialog listing those members. [`Semantic::overridable_members`]
//! lists them, [`Semantic::generate_overrides`] writes the chosen ones, and
//! the light bulb's "Generate overrides..." with the cursor on the type's
//! name writes all of them.
//!
//! Each override is what Roslyn writes: the member's accessibility (a
//! `protected internal` member of another assembly is overridden
//! `protected`), `override`, and a body that calls the base — `return
//! base.M(x);`, `get => base.P; set => base.P = value;` — or, for an
//! abstract member, throws `NotImplementedException`. Types are written as
//! the file would write them, through the type arguments the base list
//! gave.

use std::collections::HashMap;
use std::path::Path;

use rustlyn_semantics::{
    Accessibility, Detail, MethodKind, Modifiers, RefKind, SymbolId, SymbolKind, Type,
};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::fixes::support::Namer;
use super::super::{ActionKind, CodeAction, Context};
use super::members::{type_around, type_named_at_cursor};
use crate::edit::WorkspaceEdit;
use crate::semantic::{Semantic, View};

type Map = HashMap<SymbolId, Type>;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(declaration) = type_named_at_cursor(context) else {
        return;
    };
    if declaration.kind() == SyntaxKind::InterfaceDeclaration {
        return;
    }
    let candidates = overridable(context.view, &declaration);
    if candidates.is_empty() {
        return;
    }
    if let Ok(edit) = generate(context, &declaration, &candidates) {
        found.push(CodeAction {
            title: "Generate overrides...".to_string(),
            kind: ActionKind::Generate,
            fixes: None,
            edit,
        });
    }
}

impl Semantic {
    /// The inherited members the type at `offset` of `path` can override
    /// and does not yet, as the dialog lists them: `ToString()`,
    /// `Area(double)`, `Name`.
    ///
    /// # Errors
    ///
    /// When there is no type there.
    pub fn overridable_members(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
    ) -> Result<Vec<String>, String> {
        super::sources::with_context(self, path, text, TextSpan::new(offset, 0), |context| {
            let declaration = type_around(context, offset)
                .ok_or_else(|| "Place the cursor in a type.".to_string())?;
            let found = overridable(context.view, &declaration);
            Ok(found
                .iter()
                .map(|(member, map)| display(context.view, &declaration, *member, map))
                .collect())
        })
        .ok_or_else(|| "The file is not part of the project.".to_string())?
    }

    /// Overrides, in the type at `offset` of `path`, the inherited members
    /// in `members`, each named as [`Semantic::overridable_members`] lists
    /// it or by its name alone (every overload).
    ///
    /// # Errors
    ///
    /// When there is no type there, or a member is not one it can
    /// override.
    pub fn generate_overrides(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
        members: &[String],
    ) -> Result<WorkspaceEdit, String> {
        super::sources::with_context(self, path, text, TextSpan::new(offset, 0), |context| {
            let declaration = type_around(context, offset)
                .ok_or_else(|| "Place the cursor in a type.".to_string())?;
            let all = overridable(context.view, &declaration);
            let symbols = context.view.compiled().symbols();
            let mut chosen = Vec::new();
            for wanted in members {
                let matching: Vec<(SymbolId, Map)> = all
                    .iter()
                    .filter(|(member, map)| {
                        symbols.get(*member).name == *wanted
                            || display(context.view, &declaration, *member, map) == *wanted
                    })
                    .cloned()
                    .collect();
                if matching.is_empty() {
                    return Err(format!("'{wanted}' is not a member the type can override."));
                }
                chosen.extend(matching);
            }
            if chosen.is_empty() {
                return Err("Choose at least one member.".to_string());
            }
            generate(context, &declaration, &chosen)
        })
        .ok_or_else(|| "The file is not part of the project.".to_string())?
    }
}

/// Every member of the classes above the type that it can override and
/// does not: virtual, abstract or override, not sealed, not private — the
/// nearest class's version of each — with the substitution of the class's
/// construction.
pub(super) fn overridable(view: &View<'_>, declaration: &SyntaxNode) -> Vec<(SymbolId, Map)> {
    let Some(class) = view.model.declared_symbol(declaration) else {
        return Vec::new();
    };
    let symbols = view.compilation().symbols();
    let binder = view.model.binder();
    let own: Vec<SymbolId> = symbols
        .get(class)
        .members
        .iter()
        .copied()
        .filter(|&member| symbols.get(member).modifiers.contains(Modifiers::OVERRIDE))
        .collect();
    let mut taken: Vec<(SymbolId, Map)> =
        own.into_iter().map(|member| (member, Map::new())).collect();
    let mut found: Vec<(SymbolId, Map)> = Vec::new();
    let mut map: Map = HashMap::new();
    let mut current = class;
    let mut depth = 0;
    while let Some(base) = binder.base_class_of(current) {
        let base = base.substitute(&map);
        let Some(symbol) = base.symbol() else {
            break;
        };
        depth += 1;
        if symbol == class || depth > 32 {
            break;
        }
        map = binder.type_substitution(&base);
        for &member in &symbols.get(symbol).members {
            let found_member = symbols.get(member);
            let overridable_kind = match found_member.kind {
                SymbolKind::Method => found_member
                    .as_method()
                    .is_some_and(|method| method.method_kind == MethodKind::Ordinary),
                SymbolKind::Property | SymbolKind::Event => true,
                _ => false,
            };
            let modifiers = found_member.modifiers;
            if !overridable_kind || modifiers.contains(Modifiers::STATIC) {
                continue;
            }
            // What a class nearer the type declares hides what is below it,
            // a sealed override included.
            let seen = taken.iter().any(|(other, other_map)| {
                symbols.get(*other).name == found_member.name
                    && same_signature(view, *other, other_map, member, &map)
            });
            if seen {
                continue;
            }
            taken.push((member, map.clone()));
            if modifiers.contains(Modifiers::SEALED)
                || !(modifiers.contains(Modifiers::VIRTUAL)
                    || modifiers.contains(Modifiers::ABSTRACT)
                    || modifiers.contains(Modifiers::OVERRIDE))
                || matches!(
                    found_member.accessibility,
                    Accessibility::Private | Accessibility::NotApplicable
                )
                || (view.compilation().is_from_metadata(member)
                    && matches!(
                        found_member.accessibility,
                        Accessibility::Internal | Accessibility::ProtectedAndInternal
                    ))
            {
                continue;
            }
            found.push((member, map.clone()));
        }
        current = symbol;
    }
    found
}

/// Whether two members have the same kind and parameter types, each read
/// through its own substitution.
fn same_signature(view: &View<'_>, a: SymbolId, a_map: &Map, b: SymbolId, b_map: &Map) -> bool {
    let symbols = view.compilation().symbols();
    let (first, second) = (symbols.get(a), symbols.get(b));
    if first.kind != second.kind {
        return false;
    }
    let parameters = |detail: &Detail| match detail {
        Detail::Method(method) => Some((method.parameters.clone(), method.arity)),
        Detail::Property(property) => Some((property.parameters.clone(), 0)),
        Detail::Event(_) => Some((Vec::new(), 0)),
        _ => None,
    };
    let (Some((x, x_arity)), Some((y, y_arity))) =
        (parameters(&first.detail), parameters(&second.detail))
    else {
        return false;
    };
    x_arity == y_arity
        && x.len() == y.len()
        && x.iter().zip(&y).all(|(x, y)| {
            let x_type = view.model.type_of_symbol(*x).substitute(a_map);
            let y_type = view.model.type_of_symbol(*y).substitute(b_map);
            // A method's own type parameters are compared by position.
            match (x_type.value(), y_type.value()) {
                (Type::TypeParameter(_), Type::TypeParameter(_)) => true,
                (x, y) => x == y,
            }
        })
}

/// A member as the dialog lists it: `Area(double)`, `Name`, `this[int]`.
pub(super) fn display(
    view: &View<'_>,
    declaration: &SyntaxNode,
    member: SymbolId,
    map: &Map,
) -> String {
    let symbols = view.compilation().symbols();
    let namer = Namer::at(view, declaration);
    let found = symbols.get(member);
    let types = |parameters: &[SymbolId]| {
        parameters
            .iter()
            .map(|&parameter| namer.name(&view.model.type_of_symbol(parameter).substitute(map)))
            .collect::<Vec<_>>()
            .join(", ")
    };
    match &found.detail {
        Detail::Method(method) => format!("{}({})", found.name, types(&method.parameters)),
        Detail::Property(property) if property.is_indexer => {
            format!("this[{}]", types(&property.parameters))
        }
        _ => found.name.clone(),
    }
}

fn generate(
    context: &mut Context<'_, '_>,
    declaration: &SyntaxNode,
    chosen: &[(SymbolId, Map)],
) -> Result<WorkspaceEdit, String> {
    let view = &*context.view;
    let namer = Namer::at(view, declaration);
    let texts: Vec<String> = chosen
        .iter()
        .filter_map(|(member, map)| override_of(view, &namer, *member, map))
        .collect();
    let edit = super::members::append_members(declaration, &context.text, &texts)
        .ok_or_else(|| "The type's body cannot be written.".to_string())?;
    Ok(WorkspaceEdit::single(context.path.clone(), vec![edit]))
}

/// The text of an override of `member`.
fn override_of(view: &View<'_>, namer: &Namer<'_>, member: SymbolId, map: &Map) -> Option<String> {
    let symbols = view.compilation().symbols();
    let symbol = symbols.get(member);
    let access = match symbol.accessibility {
        Accessibility::ProtectedOrInternal if view.compilation().is_from_metadata(member) => {
            "protected".to_string()
        }
        other => other.to_string(),
    };
    let is_abstract = symbol.modifiers.contains(Modifiers::ABSTRACT);
    let ty = namer.name(&view.model.type_of_symbol(member).substitute(map));
    let throw = namer.not_implemented();
    let throw_expression = namer.not_implemented_expression();
    let name = &symbol.name;
    match &symbol.detail {
        Detail::Method(method) => {
            let type_parameters = if method.type_parameters.is_empty() {
                String::new()
            } else {
                let names: Vec<&str> = method
                    .type_parameters
                    .iter()
                    .map(|parameter| symbols.get(*parameter).name.as_str())
                    .collect();
                format!("<{}>", names.join(", "))
            };
            let (parameters, arguments) = parameters(view, namer, &method.parameters, map);
            let body = if is_abstract {
                throw
            } else if ty == "void" {
                format!("base.{name}{type_parameters}({arguments});")
            } else {
                format!("return base.{name}{type_parameters}({arguments});")
            };
            Some(format!(
                "{access} override {ty} {name}{type_parameters}({parameters})\n{{\n    {body}\n}}"
            ))
        }
        Detail::Property(property) => {
            let (head, target) = if property.is_indexer {
                let (parameters, arguments) = parameters(view, namer, &property.parameters, map);
                (format!("this[{parameters}]"), format!("base[{arguments}]"))
            } else {
                (name.clone(), format!("base.{name}"))
            };
            let mut accessors = Vec::new();
            let readable = property.has_get || property.getter.is_some();
            let writable = property.has_set || property.setter.is_some() || property.has_init;
            let setter = if property.has_init { "init" } else { "set" };
            if readable {
                accessors.push(if is_abstract {
                    format!("get => {throw_expression};")
                } else {
                    format!("get => {target};")
                });
            }
            if writable {
                accessors.push(if is_abstract {
                    format!("{setter} => {throw_expression};")
                } else {
                    format!("{setter} => {target} = value;")
                });
            }
            Some(format!(
                "{access} override {ty} {head} {{ {} }}",
                accessors.join(" ")
            ))
        }
        Detail::Event(_) => Some(format!("{access} override event {ty} {name};")),
        _ => None,
    }
}

/// The parameter list of an override, and the arguments that pass each
/// parameter on to the base.
fn parameters(
    view: &View<'_>,
    namer: &Namer<'_>,
    parameters: &[SymbolId],
    map: &Map,
) -> (String, String) {
    let symbols = view.compilation().symbols();
    let mut declared = Vec::new();
    let mut passed = Vec::new();
    for &parameter in parameters {
        let symbol = symbols.get(parameter);
        let detail = symbol.as_parameter();
        let modifier = match detail.map(|detail| detail.ref_kind) {
            Some(RefKind::Ref) => "ref ",
            Some(RefKind::Out) => "out ",
            Some(RefKind::In) => "in ",
            _ if detail.is_some_and(|detail| detail.is_params) => "params ",
            _ => "",
        };
        let ty = namer.name(&view.model.type_of_symbol(parameter).substitute(map));
        let name = super::super::fixes::support::escape_keyword(&symbol.name);
        declared.push(format!("{modifier}{ty} {name}"));
        let pass = if modifier == "params " { "" } else { modifier };
        passed.push(format!("{pass}{name}"));
    }
    (declared.join(", "), passed.join(", "))
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::super::support::{apply, refuses};
    use crate::semantic::tests::compile;

    const BASE: &str = "abstract class Shape<T>\n{\n    public abstract double Area();\n    public virtual string Describe(T unit, int digits) => \"\";\n    protected virtual int Sides { get; set; }\n    public virtual void Reset() { }\n    public void Plain() { }\n}\n\n";

    #[test]
    fn the_light_bulb_overrides_everything_not_overridden() {
        let source = format!(
            "{BASE}class $$Square : Shape<int>\n{{\n    public override void Reset() {{ }}\n}}\n"
        );
        assert_eq!(
            apply(&source, "Generate overrides..."),
            format!(
                "{BASE}class Square : Shape<int>\n{{\n    public override void Reset() {{ }}\n\n    public override double Area()\n    {{\n        throw new System.NotImplementedException();\n    }}\n\n    public override string Describe(int unit, int digits)\n    {{\n        return base.Describe(unit, digits);\n    }}\n\n    protected override int Sides {{ get => base.Sides; set => base.Sides = value; }}\n\n    public override string ToString()\n    {{\n        return base.ToString();\n    }}\n\n    public override bool Equals(object other)\n    {{\n        return base.Equals(other);\n    }}\n\n    public override int GetHashCode()\n    {{\n        return base.GetHashCode();\n    }}\n}}\n"
            )
        );
    }

    #[test]
    fn the_dialog_lists_and_generates_the_chosen_members() {
        let text = format!("{BASE}class Square : Shape<string>\n{{\n}}\n");
        let semantic = compile(&[("A.cs", &text)], false).expect("compiles");
        let at = text.find("Square").unwrap() as u32;
        let listed = semantic
            .overridable_members(Path::new("/p/A.cs"), at, None)
            .expect("listed");
        assert_eq!(
            listed,
            [
                "Area()",
                "Describe(string, int)",
                "Sides",
                "Reset()",
                "ToString()",
                "Equals(object)",
                "GetHashCode()"
            ]
        );
        let edit = semantic
            .generate_overrides(
                Path::new("/p/A.cs"),
                at,
                None,
                &["Describe(string, int)".to_string()],
            )
            .expect("generated");
        assert_eq!(
            crate::edit::apply(&text, edit.edits_of(Path::new("/p/A.cs"))),
            format!(
                "{BASE}class Square : Shape<string>\n{{\n    public override string Describe(string unit, int digits)\n    {{\n        return base.Describe(unit, digits);\n    }}\n}}\n"
            )
        );
    }

    #[test]
    fn a_sealed_override_ends_the_line() {
        refuses(
            "class A { public virtual void M() { } }\nclass B : A { public sealed override void M() { } public sealed override string ToString() => \"\"; public sealed override bool Equals(object o) => false; public sealed override int GetHashCode() => 0; }\nclass $$C : B { }\n",
            "Generate overrides...",
        );
    }
}
