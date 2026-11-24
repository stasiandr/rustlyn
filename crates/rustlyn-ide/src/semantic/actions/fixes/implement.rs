//! Implement interface, and implement abstract class: the members a type
//! promised and did not write, written as stubs that throw.
//!
//! The binder does not report CS0535 or CS0534 yet, so the provider works
//! out what is missing itself, the way the compiler would: every member of
//! the interface and of the interfaces it extends, with the type arguments
//! the base list gave it, that nothing in the type or its bases implements
//! with the same name and parameter types — or every abstract member of the
//! base classes that nothing on the way down overrides. It is offered with
//! the cursor on the base type in the list, or on the type's name.
//!
//! Stubs are what Roslyn writes by default: a method with a block body, a
//! property or indexer with expression-bodied accessors, a field-like event
//! (an explicit one needs `add` and `remove`), each throwing
//! `NotImplementedException`.

use std::collections::{HashMap, HashSet};

use rustlyn_semantics::{
    Accessibility, MethodKind, Modifiers, RefKind, SymbolId, SymbolKind, Type, TypeKind,
};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};

use super::super::{ActionKind, CodeAction, Context};
use super::support::{MemberPlace, Namer, insert_members};
use crate::semantic::View;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some((declaration, bases)) = bases_at(context) else {
        return;
    };
    let view = &*context.view;
    let Some(class) = view.model.declared_symbol(&declaration) else {
        return;
    };
    let symbols = view.compilation().symbols();
    let namer = Namer::at(view, &declaration);
    let abstract_class = symbols.get(class).modifiers.contains(Modifiers::ABSTRACT);
    let is_interface = symbols.get(class).type_kind() == Some(TypeKind::Interface);
    if is_interface {
        return;
    }
    for base in bases {
        let ty = view.model.type_of_syntax(&base);
        let Some(base_symbol) = ty.symbol() else {
            continue;
        };
        match symbols.get(base_symbol).type_kind() {
            Some(TypeKind::Interface) => {
                let missing = missing_interface_members(view, class, &ty);
                if missing.is_empty() {
                    continue;
                }
                let implicit: Vec<String> = missing
                    .iter()
                    .filter_map(|(member, map, _)| stub(view, &namer, *member, map, Stub::Implicit))
                    .collect();
                let explicit: Vec<String> = missing
                    .iter()
                    .filter_map(|(member, map, interface)| {
                        stub(view, &namer, *member, map, Stub::Explicit(interface))
                    })
                    .collect();
                for (title, members) in [
                    ("Implement interface", implicit),
                    ("Implement all members explicitly", explicit),
                ] {
                    if let Some(edit) =
                        insert_members(&declaration, &context.text, &members, &MemberPlace::End)
                    {
                        found.push(context.local(
                            title,
                            ActionKind::QuickFix,
                            Some("CS0535"),
                            vec![edit],
                        ));
                    }
                }
            }
            Some(TypeKind::Class | TypeKind::Record) if !abstract_class => {
                let missing = missing_abstract_members(view, class);
                let members: Vec<String> = missing
                    .iter()
                    .filter_map(|(member, map)| stub(view, &namer, *member, map, Stub::Override))
                    .collect();
                if let Some(edit) =
                    insert_members(&declaration, &context.text, &members, &MemberPlace::End)
                {
                    found.push(context.local(
                        "Implement abstract class",
                        ActionKind::QuickFix,
                        Some("CS0534"),
                        vec![edit],
                    ));
                }
            }
            _ => {}
        }
    }
}

/// The type declaration at the cursor and the base types asked about: the
/// one the cursor is on in the base list, or all of them with the cursor on
/// the type's name.
fn bases_at(context: &Context<'_, '_>) -> Option<(SyntaxNode, Vec<SyntaxNode>)> {
    let offset = context.span.start();
    let token = context.view.root.find_token(offset)?;
    let token = if token.span().start() == offset || token.span().contains(offset) {
        token
    } else {
        context.view.root.find_token(offset.checked_sub(1)?)?
    };
    let parent = token.parent().clone();
    if super::support::is_type_declaration(parent.kind())
        && token.kind() == SyntaxKind::IdentifierToken
    {
        let bases = base_types(&parent);
        return Some((parent, bases));
    }
    let base = parent
        .ancestors()
        .chain(std::iter::once(parent.clone()))
        .find(|node| node.kind() == SyntaxKind::SimpleBaseType)?;
    let declaration = base
        .parent()?
        .parent()
        .filter(|node| super::support::is_type_declaration(node.kind()))?
        .clone();
    let ty = base.children().find(|child| child.kind().is_type_node())?;
    Some((declaration, vec![ty]))
}

fn base_types(declaration: &SyntaxNode) -> Vec<SyntaxNode> {
    declaration
        .child_of_kind(SyntaxKind::BaseList)
        .map(|list| {
            list.children()
                .filter(|child| child.kind() == SyntaxKind::SimpleBaseType)
                .filter_map(|base| base.children().find(|child| child.kind().is_type_node()))
                .collect()
        })
        .unwrap_or_default()
}

/// Type parameters to what the construction said they are.
type Map = HashMap<SymbolId, Type>;

/// The members of `interface` and of every interface it extends that
/// `class` does not implement, each with the substitution that puts it in
/// the class's terms and the interface it is from.
fn missing_interface_members(
    view: &View<'_>,
    class: SymbolId,
    interface: &Type,
) -> Vec<(SymbolId, Map, Type)> {
    let symbols = view.compilation().symbols();
    let binder = view.model.binder();
    let mut missing = Vec::new();
    let mut queue = vec![interface.clone()];
    let mut visited = HashSet::new();
    while let Some(current) = queue.pop() {
        if !visited.insert(current.clone()) {
            continue;
        }
        let Some(symbol) = current.symbol() else {
            continue;
        };
        let map = binder.type_substitution(&current);
        for &member in &symbols.get(symbol).members {
            if needs_implementation(view, member) && !implemented(view, class, member, &map) {
                missing.push((member, map.clone(), current.clone()));
            }
        }
        for base in view.model.base_types_of(symbol).into_iter().rev() {
            queue.push(base.substitute(&map));
        }
    }
    missing
}

/// Whether an interface member is one an implementing type has to write:
/// not static, not a nested type, and without a body of its own.
fn needs_implementation(view: &View<'_>, member: SymbolId) -> bool {
    let compilation = view.compilation();
    let symbol = compilation.symbols().get(member);
    if symbol.modifiers.contains(Modifiers::STATIC) || symbol.name.contains('<') {
        return false;
    }
    match symbol.kind {
        SymbolKind::Method => {
            if symbol
                .as_method()
                .is_some_and(|method| method.method_kind != MethodKind::Ordinary)
            {
                return false;
            }
        }
        SymbolKind::Property | SymbolKind::Event => {}
        _ => return false,
    }
    if compilation.is_from_metadata(member) {
        return match symbol.kind {
            SymbolKind::Method => symbol.modifiers.contains(Modifiers::ABSTRACT),
            SymbolKind::Property => {
                let property = symbol.as_property();
                [
                    property.and_then(|p| p.getter),
                    property.and_then(|p| p.setter),
                ]
                .into_iter()
                .flatten()
                .any(|accessor| {
                    compilation
                        .symbols()
                        .get(accessor)
                        .modifiers
                        .contains(Modifiers::ABSTRACT)
                }) || property.is_some_and(|p| p.getter.is_none() && p.setter.is_none())
            }
            _ => true,
        };
    }
    // Declared in source: abstract unless it wrote a body.
    compilation
        .declaration_node(member)
        .is_none_or(|node| !has_body(&node))
}

fn has_body(node: &SyntaxNode) -> bool {
    let direct = |node: &SyntaxNode| {
        node.children().any(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Block | SyntaxKind::ArrowExpressionClause
            )
        })
    };
    direct(node)
        || node
            .child_of_kind(SyntaxKind::AccessorList)
            .is_some_and(|list| list.children().any(|accessor| direct(&accessor)))
}

/// Whether `class`, or a class it derives from, has a member that
/// implements `member` of an interface constructed as `map` says.
fn implemented(view: &View<'_>, class: SymbolId, member: SymbolId, map: &Map) -> bool {
    let symbols = view.compilation().symbols();
    let binder = view.model.binder();
    let name = &symbols.get(member).name;
    let explicit = format!(".{name}");
    let mut current = Some(class);
    let mut depth = 0;
    while let Some(ty) = current {
        depth += 1;
        if depth > 32 {
            break;
        }
        for &candidate in &symbols.get(ty).members {
            let found = symbols.get(candidate);
            if (found.name == *name || found.name.ends_with(&explicit))
                && same_signature(view, candidate, &HashMap::new(), member, map)
            {
                return true;
            }
        }
        current = binder
            .base_class_of(ty)
            .and_then(|base| base.symbol())
            .filter(|base| symbols.get(*base).type_kind() != Some(TypeKind::Interface));
    }
    false
}

/// Whether two members have the same kind, arity and parameter types, each
/// read through its own substitution.
pub(crate) fn same_signature(
    view: &View<'_>,
    a: SymbolId,
    a_map: &Map,
    b: SymbolId,
    b_map: &Map,
) -> bool {
    let symbols = view.compilation().symbols();
    let (first, second) = (symbols.get(a), symbols.get(b));
    if first.kind != second.kind {
        return false;
    }
    let (first_parameters, second_parameters, pairs) = match (&first.detail, &second.detail) {
        (rustlyn_semantics::Detail::Method(x), rustlyn_semantics::Detail::Method(y)) => {
            if x.arity != y.arity {
                return false;
            }
            let pairs: Vec<(SymbolId, SymbolId)> = x
                .type_parameters
                .iter()
                .copied()
                .zip(y.type_parameters.iter().copied())
                .collect();
            (x.parameters.clone(), y.parameters.clone(), pairs)
        }
        (rustlyn_semantics::Detail::Property(x), rustlyn_semantics::Detail::Property(y)) => {
            if x.is_indexer != y.is_indexer {
                return false;
            }
            (x.parameters.clone(), y.parameters.clone(), Vec::new())
        }
        (rustlyn_semantics::Detail::Event(_), rustlyn_semantics::Detail::Event(_)) => {
            return true;
        }
        _ => return false,
    };
    first_parameters.len() == second_parameters.len()
        && first_parameters
            .iter()
            .zip(&second_parameters)
            .all(|(x, y)| {
                let x_type = view.model.type_of_symbol(*x).substitute(a_map);
                let y_type = view.model.type_of_symbol(*y).substitute(b_map);
                same_type(x_type.value(), y_type.value(), &pairs)
            })
}

/// Type equality where a method's own type parameters match by position.
fn same_type(a: &Type, b: &Type, pairs: &[(SymbolId, SymbolId)]) -> bool {
    match (a, b) {
        (Type::TypeParameter(x), Type::TypeParameter(y)) => x == y || pairs.contains(&(*x, *y)),
        (
            Type::Named {
                symbol: x,
                type_arguments: xs,
            },
            Type::Named {
                symbol: y,
                type_arguments: ys,
            },
        ) => {
            x == y && xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| same_type(x, y, pairs))
        }
        (
            Type::Array {
                element: x,
                rank: xr,
            },
            Type::Array {
                element: y,
                rank: yr,
            },
        ) => xr == yr && same_type(x, y, pairs),
        (Type::Pointer(x), Type::Pointer(y)) | (Type::ByRef(x), Type::ByRef(y)) => {
            same_type(x, y, pairs)
        }
        (Type::Tuple(xs), Type::Tuple(ys)) => {
            xs.len() == ys.len()
                && xs
                    .iter()
                    .zip(ys)
                    .all(|(x, y)| same_type(&x.ty, &y.ty, pairs))
        }
        _ => a == b,
    }
}

/// The abstract members of the classes `class` derives from that nothing
/// between them and `class` overrides, with the substitution of each
/// class's construction.
fn missing_abstract_members(view: &View<'_>, class: SymbolId) -> Vec<(SymbolId, Map)> {
    let symbols = view.compilation().symbols();
    let binder = view.model.binder();
    // Every class on the way up, most derived first, with its construction.
    let mut chain: Vec<(SymbolId, Map)> = vec![(class, HashMap::new())];
    let mut map: Map = HashMap::new();
    let mut current = class;
    while let Some(base) = binder.base_class_of(current) {
        let base = base.substitute(&map);
        let Some(symbol) = base.symbol() else {
            break;
        };
        if chain.iter().any(|(seen, _)| *seen == symbol) || chain.len() > 32 {
            break;
        }
        map = binder.type_substitution(&base);
        chain.push((symbol, map.clone()));
        current = symbol;
    }
    let mut missing = Vec::new();
    for (index, (ty, ty_map)) in chain.iter().enumerate().skip(1) {
        for &member in &symbols.get(*ty).members {
            let symbol = symbols.get(member);
            if !symbol.modifiers.contains(Modifiers::ABSTRACT)
                || !matches!(
                    symbol.kind,
                    SymbolKind::Method | SymbolKind::Property | SymbolKind::Event
                )
                || symbol
                    .as_method()
                    .is_some_and(|method| method.method_kind != MethodKind::Ordinary)
            {
                continue;
            }
            let overridden = chain[..index].iter().any(|(below, below_map)| {
                symbols.get(*below).members.iter().any(|&candidate| {
                    let found = symbols.get(candidate);
                    found.name == symbol.name
                        && found.modifiers.contains(Modifiers::OVERRIDE)
                        && same_signature(view, candidate, below_map, member, ty_map)
                })
            });
            if !overridden {
                missing.push((member, ty_map.clone()));
            }
        }
    }
    missing
}

/// Which way a stub implements its member.
enum Stub<'t> {
    /// `public`, found by name.
    Implicit,
    /// Named with the interface in front, callable only through it.
    Explicit(&'t Type),
    /// `override`, with the accessibility of what it overrides.
    Override,
}

/// The text of a stub for `member`, read through `map`.
fn stub(
    view: &View<'_>,
    namer: &Namer<'_>,
    member: SymbolId,
    map: &Map,
    how: Stub<'_>,
) -> Option<String> {
    let symbols = view.compilation().symbols();
    let symbol = symbols.get(member);
    let throw = namer.not_implemented();
    let throw_expression = namer.not_implemented_expression();
    let ty = namer.name(&view.model.type_of_symbol(member).substitute(map));
    let (prefix, name) = match how {
        Stub::Implicit => ("public ".to_string(), symbol.name.clone()),
        Stub::Explicit(interface) => (
            String::new(),
            format!("{}.{}", namer.name(interface), symbol.name),
        ),
        Stub::Override => {
            let access = match symbol.accessibility {
                Accessibility::NotApplicable => Accessibility::Public,
                other => other,
            };
            (format!("{access} override "), symbol.name.clone())
        }
    };
    let explicit = matches!(how, Stub::Explicit(_));
    match &symbol.detail {
        rustlyn_semantics::Detail::Method(method) => {
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
            let constraints = if matches!(how, Stub::Implicit) {
                constraints(view, namer, &method.type_parameters, map)
            } else {
                String::new()
            };
            let parameters = parameter_list(view, namer, &method.parameters, map);
            Some(format!(
                "{prefix}{ty} {name}{type_parameters}({parameters}){constraints}\n{{\n    {throw}\n}}"
            ))
        }
        rustlyn_semantics::Detail::Property(property) => {
            let mut accessors = Vec::new();
            if property.has_get || property.getter.is_some() {
                accessors.push(format!("get => {throw_expression};"));
            }
            if property.has_init {
                accessors.push(format!("init => {throw_expression};"));
            } else if property.has_set || property.setter.is_some() {
                accessors.push(format!("set => {throw_expression};"));
            }
            let head = if property.is_indexer {
                let parameters = parameter_list(view, namer, &property.parameters, map);
                let this = match how {
                    Stub::Explicit(interface) => format!("{}.this", namer.name(interface)),
                    _ => "this".to_string(),
                };
                format!("{this}[{parameters}]")
            } else {
                name
            };
            Some(format!("{prefix}{ty} {head} {{ {} }}", accessors.join(" ")))
        }
        rustlyn_semantics::Detail::Event(_) if explicit => Some(format!(
            "event {ty} {name}\n{{\n    add\n    {{\n        {throw}\n    }}\n\n    remove\n    {{\n        {throw}\n    }}\n}}"
        )),
        rustlyn_semantics::Detail::Event(_) => {
            // `public override event` needs the order `override` then `event`.
            Some(format!("{prefix}event {ty} {name};"))
        }
        _ => None,
    }
}

/// `ref int a, params string[] rest`.
pub(crate) fn parameter_list(
    view: &View<'_>,
    namer: &Namer<'_>,
    parameters: &[SymbolId],
    map: &Map,
) -> String {
    let symbols = view.compilation().symbols();
    parameters
        .iter()
        .map(|&parameter| {
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
            format!("{modifier}{ty} {}", symbol.name)
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// ` where T : class, IComparable<T>, new()` for the type parameters that
/// have constraints.
fn constraints(view: &View<'_>, namer: &Namer<'_>, parameters: &[SymbolId], map: &Map) -> String {
    let symbols = view.compilation().symbols();
    let binder = view.model.binder();
    let mut out = String::new();
    for &parameter in parameters {
        let Some(detail) = symbols.get(parameter).as_type_parameter() else {
            continue;
        };
        let mut parts: Vec<String> = Vec::new();
        if detail.reference_type {
            parts.push("class".to_string());
        } else if detail.value_type {
            parts.push("struct".to_string());
        }
        for constraint in &detail.constraints {
            let mut sink = rustlyn_semantics::Diagnostics::new();
            let ty = binder
                .resolve_type_ref(*constraint, &mut sink)
                .substitute(map);
            if !ty.is_error() {
                parts.push(namer.name(&ty));
            }
        }
        if detail.constructor && !detail.value_type {
            parts.push("new()".to_string());
        }
        if !parts.is_empty() {
            out.push_str(&format!(
                " where {} : {}",
                symbols.get(parameter).name,
                parts.join(", ")
            ));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::super::tests::{fix, titles};

    const SHAPE: &str = "interface IShape\n{\n    int Area();\n    string Name { get; set; }\n}\n";

    #[test]
    fn an_interface_is_implemented_with_stubs() {
        let source = "using System;\n\nclass Circle : $$IShape\n{\n    int radius;\n}\n";
        assert_eq!(
            fix(&[source, SHAPE], "Implement interface"),
            "using System;\n\nclass Circle : IShape\n{\n    int radius;\n\n    public int Area()\n    {\n        throw new NotImplementedException();\n    }\n\n    public string Name { get => throw new NotImplementedException(); set => throw new NotImplementedException(); }\n}\n"
        );
    }

    #[test]
    fn an_empty_body_on_one_line_is_opened_up() {
        let source = "class $$Circle : IShape { }\n";
        assert_eq!(
            fix(&[source, SHAPE], "Implement all members explicitly"),
            "class Circle : IShape\n{\n    int IShape.Area()\n    {\n        throw new System.NotImplementedException();\n    }\n\n    string IShape.Name { get => throw new System.NotImplementedException(); set => throw new System.NotImplementedException(); }\n}\n"
        );
    }

    #[test]
    fn what_is_already_there_is_not_written_again() {
        let source = "class Circle : $$IShape\n{\n    public int Area() => 1;\n}\n";
        assert_eq!(
            fix(&[source, SHAPE], "Implement interface"),
            "class Circle : IShape\n{\n    public int Area() => 1;\n\n    public string Name { get => throw new System.NotImplementedException(); set => throw new System.NotImplementedException(); }\n}\n"
        );
        let done = "class Circle : $$IShape\n{\n    public int Area() => 1;\n    public string Name { get; set; }\n}\n";
        assert!(!titles(&[done, SHAPE]).contains(&"Implement interface".to_string()));
    }

    #[test]
    fn type_arguments_modifiers_and_generics_carry_over() {
        let interface = "interface IStore<T>\n{\n    bool TryGet(int key, out T value);\n    void Put(ref T item, params T[] more);\n    U Convert<U>(T item) where U : class, new();\n    T this[int index] { get; }\n    event System.Action<T> Changed;\n    int Count { get; init; }\n}\n";
        let source = "using System;\nusing System.Collections.Generic;\n\nclass Store : $$IStore<List<string>>\n{\n}\n";
        assert_eq!(
            fix(&[source, interface], "Implement interface"),
            "using System;\nusing System.Collections.Generic;\n\nclass Store : IStore<List<string>>\n{\n    public bool TryGet(int key, out List<string> value)\n    {\n        throw new NotImplementedException();\n    }\n\n    public void Put(ref List<string> item, params List<string>[] more)\n    {\n        throw new NotImplementedException();\n    }\n\n    public U Convert<U>(List<string> item) where U : class, new()\n    {\n        throw new NotImplementedException();\n    }\n\n    public List<string> this[int index] { get => throw new NotImplementedException(); }\n\n    public event Action<List<string>> Changed;\n\n    public int Count { get => throw new NotImplementedException(); init => throw new NotImplementedException(); }\n}\n"
        );
    }

    #[test]
    fn an_explicit_event_has_accessors() {
        let interface = "interface INotify { event System.Action Changed; }\n";
        let source = "class Model : $$INotify\n{\n}\n";
        assert_eq!(
            fix(&[source, interface], "Implement all members explicitly"),
            "class Model : INotify\n{\n    event System.Action INotify.Changed\n    {\n        add\n        {\n            throw new System.NotImplementedException();\n        }\n\n        remove\n        {\n            throw new System.NotImplementedException();\n        }\n    }\n}\n"
        );
    }

    #[test]
    fn inherited_interfaces_are_implemented_too() {
        let interface =
            "interface IBase { void Run(); }\ninterface IDerived : IBase { void Stop(); }\n";
        let source = "class Machine : $$IDerived\n{\n}\n";
        assert_eq!(
            fix(&[source, interface], "Implement interface"),
            "class Machine : IDerived\n{\n    public void Stop()\n    {\n        throw new System.NotImplementedException();\n    }\n\n    public void Run()\n    {\n        throw new System.NotImplementedException();\n    }\n}\n"
        );
    }

    #[test]
    fn a_base_class_implementation_counts() {
        let interface = "interface IRun { void Run(); }\nclass Runner { public void Run() { } }\n";
        let source = "class Fast : Runner, $$IRun\n{\n}\n";
        assert!(!titles(&[source, interface]).contains(&"Implement interface".to_string()));
    }

    #[test]
    fn a_default_implementation_is_left_alone() {
        let interface =
            "interface IGreet { string Name { get; } string Greet() => \"Hi \" + Name; }\n";
        let source = "class Person : $$IGreet\n{\n}\n";
        assert_eq!(
            fix(&[source, interface], "Implement interface"),
            "class Person : IGreet\n{\n    public string Name { get => throw new System.NotImplementedException(); }\n}\n"
        );
    }

    #[test]
    fn an_abstract_class_is_implemented_with_overrides() {
        let base = "abstract class Animal<T>\n{\n    public abstract void Eat(T food);\n    protected abstract int Legs { get; }\n    public virtual void Sleep() { }\n}\nabstract class Pet : Animal<string>\n{\n    public override void Eat(string food) { }\n    public abstract string Owner { get; set; }\n}\n";
        let source = "using System;\n\nclass Dog : $$Pet\n{\n}\n";
        assert_eq!(
            fix(&[source, base], "Implement abstract class"),
            "using System;\n\nclass Dog : Pet\n{\n    public override string Owner { get => throw new NotImplementedException(); set => throw new NotImplementedException(); }\n\n    protected override int Legs { get => throw new NotImplementedException(); }\n}\n"
        );
    }

    #[test]
    fn an_abstract_class_is_not_asked_to_implement() {
        let base = "abstract class Animal { public abstract void Eat(); }\n";
        let source = "abstract class Dog : $$Animal\n{\n}\n";
        assert!(!titles(&[source, base]).contains(&"Implement abstract class".to_string()));
    }
}
