//! Resolving names to symbols and type syntax to types.

use rustlyn_diagnostics::ErrorCode;
use rustlyn_semantics::{BoundSymbol, Compilation, SemanticModel, SymbolKind, Type};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, parse};
use rustlyn_text::SourceText;

fn compile(text: &str) -> Compilation {
    Compilation::create(vec![parse(SourceText::new("Program.cs", text))])
}

fn compile_many(sources: &[&str]) -> Compilation {
    Compilation::create(
        sources
            .iter()
            .enumerate()
            .map(|(index, text)| parse(SourceText::new(format!("File{index}.cs"), *text)))
            .collect(),
    )
}

/// The model for the user's file, which is the one after the core library.
fn model(compilation: &Compilation) -> SemanticModel<'_> {
    SemanticModel::new(compilation, 1)
}

/// The first node of `kind` in the user's file.
fn first(compilation: &Compilation, kind: SyntaxKind) -> SyntaxNode {
    compilation.source_trees()[0]
        .root()
        .descendants()
        .find(|node| node.kind() == kind)
        .unwrap_or_else(|| panic!("no {kind:?} in the source"))
}

/// The type of the first declaration of `kind`, as it reads.
fn declared_type(text: &str, kind: SyntaxKind) -> String {
    let compilation = compile(text);
    let model = model(&compilation);
    let node = first(&compilation, kind);
    model.declared_type(&node).display(compilation.symbols())
}

// -- types -----------------------------------------------------------------

#[test]
fn keywords_resolve_to_the_types_they_name() {
    for (source, expected) in [
        ("class C { int f; }", "int"),
        ("class C { string f; }", "string"),
        ("class C { object f; }", "object"),
        ("class C { bool f; }", "bool"),
        ("class C { double f; }", "double"),
    ] {
        assert_eq!(
            declared_type(source, SyntaxKind::VariableDeclarator),
            expected,
            "for {source:?}"
        );
    }
}

#[test]
fn names_resolve_to_declared_types() {
    assert_eq!(
        declared_type(
            "class Other {} class C { Other f; }",
            SyntaxKind::VariableDeclarator
        ),
        "Other"
    );
    assert_eq!(
        declared_type(
            "namespace N { class Other {} class C { Other f; } }",
            SyntaxKind::VariableDeclarator
        ),
        "Other"
    );
    assert_eq!(
        declared_type(
            "namespace N { class Other {} }\nclass C { N.Other f; }",
            SyntaxKind::VariableDeclarator
        ),
        "Other"
    );
}

#[test]
fn constructed_generics_keep_their_arguments() {
    assert_eq!(
        declared_type(
            "using System.Collections.Generic;\nclass C { List<int> f; }",
            SyntaxKind::VariableDeclarator
        ),
        "List<int>"
    );
    assert_eq!(
        declared_type(
            "using System.Collections.Generic;\nclass C { Dictionary<string, List<int>> f; }",
            SyntaxKind::VariableDeclarator
        ),
        "Dictionary<string, List<int>>"
    );
}

#[test]
fn arrays_pointers_and_tuples() {
    assert_eq!(
        declared_type("class C { int[] f; }", SyntaxKind::VariableDeclarator),
        "int[]"
    );
    assert_eq!(
        declared_type("class C { int[,] f; }", SyntaxKind::VariableDeclarator),
        "int[,]"
    );
    assert_eq!(
        declared_type("class C { int[][] f; }", SyntaxKind::VariableDeclarator),
        "int[][]"
    );
    assert_eq!(
        declared_type(
            "class C { (int a, string b) f; }",
            SyntaxKind::VariableDeclarator
        ),
        "(int a, string b)"
    );
    assert_eq!(
        declared_type("class C { unsafe int* f; }", SyntaxKind::VariableDeclarator),
        "int*"
    );
}

#[test]
fn nullable_value_types_are_constructed_but_reference_ones_are_not() {
    assert_eq!(
        declared_type("class C { int? f; }", SyntaxKind::VariableDeclarator),
        "Nullable<int>"
    );
    // Nullability of a reference type is an annotation, not a different type.
    assert_eq!(
        declared_type("class C { string? f; }", SyntaxKind::VariableDeclarator),
        "string"
    );
}

#[test]
fn type_parameters_resolve_to_themselves() {
    assert_eq!(
        declared_type("class C<T> { T f; }", SyntaxKind::VariableDeclarator),
        "T"
    );
    assert_eq!(
        declared_type("class C { void M<T>(T value) {} }", SyntaxKind::Parameter),
        "T"
    );
}

#[test]
fn using_directives_bring_namespaces_into_scope() {
    // Without the using, the name cannot be found.
    let compilation = compile("class C { List<int> f; }");
    assert!(
        compilation
            .semantic_diagnostics()
            .iter()
            .any(|entry| entry.diagnostic.code() == ErrorCode::ErrSingleTypeNameNotFound)
    );

    let compilation = compile("using System.Collections.Generic;\nclass C { List<int> f; }");
    assert!(compilation.semantic_diagnostics().is_empty());
}

#[test]
fn a_using_alias_renames_a_type() {
    let compilation =
        compile("using Numbers = System.Collections.Generic.List<int>;\nclass C { Numbers f; }");
    let model = model(&compilation);
    let node = first(&compilation, SyntaxKind::VariableDeclarator);
    assert_eq!(
        model.declared_type(&node).display(compilation.symbols()),
        "List<int>"
    );
}

#[test]
fn a_global_using_reaches_every_file() {
    let compilation = compile_many(&[
        "global using System.Collections.Generic;",
        "class C { List<int> f; }",
    ]);
    let model = SemanticModel::new(&compilation, 2);
    let node = compilation.source_trees()[1]
        .root()
        .descendants()
        .find(|node| node.kind() == SyntaxKind::VariableDeclarator)
        .expect("the field");
    assert_eq!(
        model.declared_type(&node).display(compilation.symbols()),
        "List<int>"
    );
}

/// Names in a file being typed in, every scope of which holds the edit. Each
/// name asked for the `using`s of each namespace around it, which were
/// resolved again every time, and asked whether each namespace was the edit's
/// by walking to the root: a thousand nested namespaces made every name cost
/// the square of the depth (found by fuzzing, `examples/fuzz.rs` in
/// rustlyn-ide).
#[test]
fn names_in_a_file_being_edited_find_their_scopes_once() {
    let asking = std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(|| {
            let text = |statement: &str| {
                format!(
                    "using System;\nusing System.Collections.Generic;\n\
                     {}class C {{ void M() {{ int x = 1; {statement} }} }}{}",
                    "namespace N { ".repeat(1000),
                    " }".repeat(1000)
                )
            };
            let old = text("x++;");
            let compilation = compile(&old);
            let edited = parse(SourceText::new("Program.cs", text("x += 2;")));
            let model = SemanticModel::speculative(
                &compilation,
                rustlyn_semantics::Speculation::new(1, &old, &edited),
            );
            let started = std::time::Instant::now();
            for name in edited
                .root()
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::IdentifierName)
            {
                let _ = model.symbol_at(&name);
            }
            assert!(
                started.elapsed().as_secs() < 5,
                "took {:?}",
                started.elapsed()
            );
        })
        .expect("a thread to ask on");
    asking.join().expect("the questions");
}

/// A body is bound as deep as it nests, and the editor asks from whatever
/// thread it is on: the model binds on a stack of its own, so a chain of
/// thousands of terms (generated code) does not take the editor down with
/// the two megabytes of a test thread.
#[test]
fn a_body_of_thousands_of_terms_is_bound_on_any_thread() {
    let text = format!(
        "class C {{ int M(int a) {{ return a{}; }} }}",
        " + a".repeat(5000)
    );
    let compilation = compile(&text);
    let model = model(&compilation);
    let owner = first(&compilation, SyntaxKind::MethodDeclaration);
    assert!(model.bind_body(&owner).diagnostics.is_empty());
    assert!(model.bind_body_for_editor(&owner).diagnostics.is_empty());
    let name = compilation.source_trees()[0]
        .root()
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::IdentifierName)
        .last()
        .expect("the last term");
    assert_eq!(model.type_of(&name).display(compilation.symbols()), "int");
    assert!(model.body_diagnostics().is_empty());
}

#[test]
fn an_inner_scope_wins_over_an_outer_one() {
    let compilation = compile(
        "class Shadowed {}
         namespace N { class Shadowed {} class C { Shadowed f; } }",
    );
    let model = model(&compilation);
    let node = first(&compilation, SyntaxKind::VariableDeclarator);
    let ty = model.declared_type(&node);
    let symbol = ty.symbol().expect("a named type");
    assert_eq!(
        compilation.symbols().qualified_name(symbol),
        "N.Shadowed",
        "the namespace's own type should win over the global one"
    );
}

#[test]
fn a_using_of_an_inner_declaration_comes_before_an_outer_namespace() {
    // Each namespace's members, then the `using`s of the declaration of it,
    // outwards (§7.8.1): `Z.Y`'s declaration imports `V`, whose `T` is found
    // before `Z` is asked for one of its own.
    let compilation = compile(
        "namespace Z {
             class T {}
             namespace Y {
                 using V;
                 namespace X { class C { T f; } }
             }
         }
         namespace V { class T {} }",
    );
    let model = model(&compilation);
    let node = first(&compilation, SyntaxKind::VariableDeclarator);
    let symbol = model.declared_type(&node).symbol().expect("a named type");
    assert_eq!(compilation.symbols().qualified_name(symbol), "V.T");
}

#[test]
fn nested_types_are_visible_from_inside_and_through_a_base() {
    let compilation = compile(
        "class Base { public class Nested {} }
         class Derived : Base { Nested f; }",
    );
    assert!(
        compilation.semantic_diagnostics().is_empty(),
        "{:?}",
        compilation.semantic_diagnostics()
    );
    let model = model(&compilation);
    let node = first(&compilation, SyntaxKind::VariableDeclarator);
    assert_eq!(
        model.declared_type(&node).display(compilation.symbols()),
        "Base.Nested"
    );
}

#[test]
fn arity_decides_which_type_a_name_means() {
    let compilation = compile("class P {} class P<T> {} class C { P<int> a; P b; }");
    let model = model(&compilation);
    let fields: Vec<_> = compilation.source_trees()[0]
        .root()
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::VariableDeclarator)
        .map(|node| model.declared_type(&node).display(compilation.symbols()))
        .collect();
    assert_eq!(fields, vec!["P<int>", "P"]);
}

// -- base types ------------------------------------------------------------

#[test]
fn base_types_resolve() {
    let compilation = compile("interface I {} class Base {} class Derived : Base, I {}");
    let model = model(&compilation);
    let node = compilation.source_trees()[0]
        .root()
        .descendants()
        .find(|node| {
            node.kind() == SyntaxKind::ClassDeclaration
                && node
                    .child_token_of_kind(SyntaxKind::IdentifierToken)
                    .is_some_and(|token| token.text() == "Derived")
        })
        .expect("the derived class");
    let symbol = model.declared_symbol(&node).expect("a symbol");
    let names: Vec<_> = model
        .base_types_of(symbol)
        .iter()
        .map(|ty| ty.display(compilation.symbols()))
        .collect();
    assert_eq!(names, vec!["Base", "I"]);
}

#[test]
fn an_unknown_type_is_reported_once_and_does_not_cascade() {
    let compilation = compile("class C { Missing f; }");
    let diagnostics = compilation.semantic_diagnostics();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(
        diagnostics[0].diagnostic.code(),
        ErrorCode::ErrSingleTypeNameNotFound
    );
    assert_eq!(
        diagnostics[0].diagnostic.message(),
        "The type or namespace name 'Missing' could not be found (are you missing a using directive or an assembly reference?)"
    );

    let model = model(&compilation);
    let node = first(&compilation, SyntaxKind::VariableDeclarator);
    assert_eq!(model.declared_type(&node), Type::Error);
}

// -- the model -------------------------------------------------------------

#[test]
fn a_declaration_node_leads_back_to_its_symbol() {
    let compilation = compile("namespace N { class C { void M(int x) {} } }");
    let model = model(&compilation);
    let symbols = compilation.symbols();

    for (kind, expected) in [
        (SyntaxKind::NamespaceDeclaration, "N"),
        (SyntaxKind::ClassDeclaration, "N.C"),
        (SyntaxKind::MethodDeclaration, "N.C.M"),
        (SyntaxKind::Parameter, "N.C.M.x"),
    ] {
        let node = first(&compilation, kind);
        let symbol = model.declared_symbol(&node).expect("a symbol");
        assert_eq!(symbols.qualified_name(symbol), expected);
    }
}

#[test]
fn a_name_in_a_type_position_resolves_to_its_type() {
    let compilation = compile("namespace N { class Target {} class C { Target f; } }");
    let model = model(&compilation);
    let name = compilation.source_trees()[0]
        .root()
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IdentifierName && node.text() == "Target")
        .expect("the type name");
    let symbol = model.symbol_at(&name).expect("a symbol");
    assert_eq!(compilation.symbols().qualified_name(symbol), "N.Target");
    assert_eq!(
        compilation.symbols().get(symbol).kind,
        SymbolKind::NamedType
    );
}

#[test]
fn a_qualified_name_resolves_part_by_part() {
    let compilation = compile("class C { System.Collections.Generic.List<int> f; }");
    let model = model(&compilation);
    let symbols = compilation.symbols();
    let names: Vec<_> = compilation.source_trees()[0]
        .root()
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::IdentifierName)
        .filter_map(|node| model.symbol_at(&node))
        .map(|symbol| symbols.qualified_name(symbol))
        .collect();
    assert!(names.contains(&"System".to_string()));
    assert!(names.contains(&"System.Collections.Generic".to_string()));
}

// -- what a bound body records ----------------------------------------------

/// What a bound body records for the `n`th name spelled `text` in the
/// method `M`: the symbol its token settled on, and what the name refers to,
/// each as its qualified name, or `local` for a local.
fn recorded(source: &str, text: &str, n: usize) -> (Option<String>, Option<String>) {
    let compilation = compile(source);
    let model = model(&compilation);
    let method = compilation.source_trees()[0]
        .root()
        .descendants()
        .find(|node| {
            node.kind() == SyntaxKind::MethodDeclaration
                && node
                    .child_tokens()
                    .any(|token| token.kind() == SyntaxKind::IdentifierToken && token.text() == "M")
        })
        .expect("a method M");
    let body = model.bind_body(&method);
    let token = method
        .descendant_tokens()
        .filter(|token| token.kind() == SyntaxKind::IdentifierToken && token.text() == text)
        .nth(n)
        .unwrap_or_else(|| panic!("no {text} #{n}"));
    let symbols = compilation.symbols();
    let symbol = body
        .symbols
        .get(&token.span())
        .map(|id| symbols.qualified_name(*id));
    let reference = body
        .references
        .get(&token.parent().span())
        .map(|found| match found {
            BoundSymbol::Declared(id) => symbols.qualified_name(*id),
            BoundSymbol::Local(_) => "local".to_string(),
        });
    (symbol, reference)
}

#[test]
fn a_bound_body_records_every_name_it_binds() {
    let source = r#"
using System;
struct Step { public int A; }
class Box<T> { public Box(int n) {} }
class Model { public int Field; public int Prop { get; set; } public Action Act; public Func<int, int> Fn { get; set; } }
class C
{
    Action field;
    Action Prop { get; set; }
    void M(Action action)
    {
        var made = new Model { Field = 1, Prop = 2 };
        Model local = made;
        Func<Model, int> read = (Model x) => x.Field;
        var box = new Box<Step>(3);
        System.Collections.Generic.List<Step> steps = null;
        action(); field(); Prop(); made.Act(); made.Fn(3);
        Action held = null; held();
    }
}
"#;
    let named = |name: &str| Some(name.to_string());
    // A member an object initializer sets, as `x.Field` would be.
    assert_eq!(
        recorded(source, "Field", 0),
        (named("Model.Field"), named("Model.Field"))
    );
    assert_eq!(
        recorded(source, "Prop", 0),
        (named("Model.Prop"), named("Model.Prop"))
    );
    // Types where a type is written: a local's, a lambda parameter's, a type
    // argument of a construction, and the namespaces before a dotted one.
    assert_eq!(
        recorded(source, "Model", 1),
        (named("Model"), named("Model"))
    );
    assert_eq!(
        recorded(source, "Model", 3),
        (named("Model"), named("Model"))
    );
    assert_eq!(recorded(source, "Step", 0), (named("Step"), named("Step")));
    assert_eq!(recorded(source, "Func", 0).0, named("System.Func`2"));
    assert_eq!(
        recorded(source, "Generic", 0),
        (
            named("System.Collections.Generic"),
            named("System.Collections.Generic")
        )
    );
    assert_eq!(recorded(source, "Step", 1), (named("Step"), named("Step")));
    // `new Box<Step>` is the constructor called, of the type named.
    assert_eq!(recorded(source, "Box", 0).0, named("Box`1..ctor"));
    // A delegate called through a name: the call is to `Invoke`, and the
    // name is the variable, parameter, field or property that holds it,
    // whether written alone or after a dot.
    for (name, holder) in [
        ("action", "C.M.action"),
        ("field", "C.field"),
        ("Prop", "C.Prop"),
        ("Act", "Model.Act"),
        ("Fn", "Model.Fn"),
    ] {
        let at = if name == "Prop" {
            1
        } else {
            usize::from(name == "action")
        };
        let (symbol, reference) = recorded(source, name, at);
        assert!(
            symbol.is_some_and(|symbol| symbol.ends_with(".Invoke")),
            "{name}"
        );
        assert_eq!(reference, named(holder), "{name}");
    }
    let (symbol, reference) = recorded(source, "held", 1);
    assert_eq!(symbol, named("System.Action.Invoke"));
    assert_eq!(reference, named("local"));
}

#[test]
fn a_file_that_is_one_namespace_keeps_the_usings_inside_it() {
    // The compilation unit of a file that is one namespace declaration and
    // nothing else spans exactly what the declaration spans, and the
    // `using`s of each were kept under the same key: whichever was asked
    // first gave its own to both — none, where the unit was, so that every
    // name the namespace imports went missing (`ValueType` in Unity's
    // `ObjectDumper`, now and then, as threads raced to it).
    let source =
        "namespace N\n{\n    using System;\n    class C { bool M(object o) => o is ValueType; }\n}";
    let compilation = compile(source);
    let model = model(&compilation);
    let root = compilation.source_trees()[0].root();
    let _ = model.binder().context_at(1, &root);
    let errors: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(errors.is_empty(), "{errors:#?}");
}

/// Two edits a file apart leave the text between them as it was, moved by
/// what the first one typed: a declaration there is the one compiled.
#[test]
fn a_speculation_maps_what_lies_between_two_edits() {
    use rustlyn_text::TextSpan;
    let old = "class A { }\n\nclass B { int x; }\n\nclass C { }\n";
    let new = "// typed\nclass A { }\n\nclass B { int yy; }\n\nclass C { }\n";
    let edited = parse(SourceText::new("Program.cs", new));
    let speculation = rustlyn_semantics::Speculation::new(1, old, &edited);
    let span_of = |text: &str, part: &str| {
        let at = text.find(part).expect("in the text");
        TextSpan::new(at as u32, part.len() as u32)
    };
    for part in ["class A { }", "class C { }"] {
        assert_eq!(
            speculation.map(span_of(new, part)),
            Some(span_of(old, part))
        );
        assert_eq!(
            speculation.unmap(span_of(old, part)),
            Some(span_of(new, part))
        );
    }
    // A declaration with the second edit inside it, its ends untouched.
    assert_eq!(
        speculation.map(span_of(new, "class B { int yy; }")),
        Some(span_of(old, "class B { int x; }"))
    );
    // What was typed in place of something is where that was; what ends
    // inside it, or was typed where nothing was, has no counterpart.
    assert_eq!(speculation.map(span_of(new, "yy")), Some(span_of(old, "x")));
    let inside = TextSpan::new(span_of(new, "yy").start(), 1);
    assert_eq!(speculation.map(inside), None);
    assert_eq!(speculation.map(span_of(new, "// typed")), None);
}
