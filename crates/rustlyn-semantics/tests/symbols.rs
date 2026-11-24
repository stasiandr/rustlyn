//! The declaration table.

use rustlyn_diagnostics::ErrorCode;
use rustlyn_semantics::{
    Accessibility, Compilation, MethodKind, Modifiers, SpecialType, SymbolId, SymbolKind, TypeKind,
};
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

fn compile(sources: &[&str]) -> Compilation {
    Compilation::create_without_corlib(
        sources
            .iter()
            .enumerate()
            .map(|(index, text)| parse(SourceText::new(format!("File{index}.cs"), *text)))
            .collect(),
    )
}

/// The one symbol at `path`, by qualified name.
fn find(compilation: &Compilation, path: &str) -> SymbolId {
    compilation
        .symbols()
        .iter()
        .find(|symbol| compilation.symbols().qualified_name(symbol.id) == path)
        .unwrap_or_else(|| panic!("no symbol named {path}"))
        .id
}

/// The names of a container's members, in declaration order.
fn member_names(compilation: &Compilation, path: &str) -> Vec<String> {
    let symbols = compilation.symbols();
    symbols
        .get(find(compilation, path))
        .members
        .iter()
        .map(|id| symbols.get(*id).name.clone())
        .collect()
}

fn codes(compilation: &Compilation) -> Vec<ErrorCode> {
    compilation
        .diagnostics()
        .iter()
        .map(|entry| entry.diagnostic.code())
        .collect()
}

// -- namespaces ------------------------------------------------------------

#[test]
fn a_dotted_namespace_is_a_chain_of_namespaces() {
    let compilation = compile(&["namespace A.B.C { class X {} }"]);
    let symbols = compilation.symbols();
    assert_eq!(
        symbols.get(find(&compilation, "A")).kind,
        SymbolKind::Namespace
    );
    assert_eq!(
        symbols.get(find(&compilation, "A.B.C.X")).kind,
        SymbolKind::NamedType
    );
}

#[test]
fn namespaces_merge_across_blocks_and_files() {
    let compilation = compile(&[
        "namespace N { class A {} }",
        "namespace N { class B {} }\nnamespace N.Inner { class C {} }",
    ]);
    assert_eq!(member_names(&compilation, "N"), vec!["A", "B", "Inner"]);
    assert_eq!(
        compilation
            .symbols()
            .get(find(&compilation, "N"))
            .locations
            .len(),
        3,
        "each block should be recorded as a location of the same namespace"
    );
}

#[test]
fn a_file_scoped_namespace_holds_the_rest_of_the_file() {
    let compilation = compile(&["namespace N;\nclass A {}\nclass B {}"]);
    assert_eq!(member_names(&compilation, "N"), vec!["A", "B"]);
}

// -- types -----------------------------------------------------------------

#[test]
fn partial_declarations_become_one_type() {
    let compilation = compile(&[
        "partial class C { void First() {} }",
        "partial class C { void Second() {} }",
    ]);
    assert!(!compilation.has_errors(), "{:?}", codes(&compilation));
    // The `.ctor` after them is the one a class with no constructor still
    // has, and the merged type has exactly one of it. It comes last because
    // whether it is needed is not known until every part has been read.
    assert_eq!(
        member_names(&compilation, "C"),
        vec!["First", "Second", ".ctor"]
    );
    assert_eq!(
        compilation
            .symbols()
            .get(find(&compilation, "C"))
            .locations
            .len(),
        2
    );
}

#[test]
fn declaring_the_same_type_twice_without_partial_is_an_error() {
    let compilation = compile(&["class C {}\nclass C {}"]);
    assert_eq!(codes(&compilation), vec![ErrorCode::ErrDuplicateNameInNS]);
}

#[test]
fn arity_is_part_of_a_types_identity() {
    let compilation = compile(&["class C {}\nclass C<T> {}\nclass C<T, U> {}"]);
    assert!(!compilation.has_errors(), "{:?}", codes(&compilation));
    let symbols = compilation.symbols();
    let names: Vec<_> = compilation
        .all_types()
        .map(rustlyn_semantics::Symbol::metadata_name)
        .collect();
    assert_eq!(names, vec!["C", "C`1", "C`2"]);
    assert_eq!(
        symbols
            .get(find(&compilation, "C`1"))
            .as_named_type()
            .unwrap()
            .type_parameters
            .len(),
        1
    );
}

#[test]
fn every_flavour_of_type_is_recognised() {
    let compilation = compile(&[
        "class C {} struct S {} interface I {} enum E {} delegate void D(); \
         record R(int X); record struct RS(int Y);",
    ]);
    let symbols = compilation.symbols();
    let kind = |name: &str| symbols.get(find(&compilation, name)).type_kind();
    assert_eq!(kind("C"), Some(TypeKind::Class));
    assert_eq!(kind("S"), Some(TypeKind::Struct));
    assert_eq!(kind("I"), Some(TypeKind::Interface));
    assert_eq!(kind("E"), Some(TypeKind::Enum));
    assert_eq!(kind("D"), Some(TypeKind::Delegate));
    assert_eq!(kind("R"), Some(TypeKind::Record));
    assert_eq!(kind("RS"), Some(TypeKind::RecordStruct));
}

#[test]
fn nested_types_belong_to_their_container() {
    let compilation = compile(&["class Outer { class Inner { class Deepest {} } }"]);
    assert_eq!(
        compilation
            .symbols()
            .get(find(&compilation, "Outer.Inner.Deepest"))
            .kind,
        SymbolKind::NamedType
    );
}

#[test]
fn base_types_are_recorded_for_later() {
    let compilation = compile(&["class A {} interface I {} class B : A, I {}"]);
    let symbols = compilation.symbols();
    let b = symbols
        .get(find(&compilation, "B"))
        .as_named_type()
        .unwrap();
    assert_eq!(
        b.base_types.len(),
        2,
        "both the base class and the interface"
    );
}

// -- members ---------------------------------------------------------------

#[test]
fn members_of_every_kind() {
    let compilation = compile(&["class C {
            int _field;
            const int Constant = 1;
            public int Property { get; set; }
            public int this[int i] { get => i; }
            public event System.Action Changed;
            public C(int x) {}
            static C() {}
            ~C() {}
            void Method<T>(T value, params int[] rest) {}
            public static C operator +(C a, C b) => a;
            public static implicit operator int(C c) => 0;
        }"]);
    assert_eq!(
        member_names(&compilation, "C"),
        vec![
            "_field",
            "Constant",
            "Property",
            "this[]",
            "Changed",
            ".ctor",
            ".cctor",
            "Finalize",
            "Method",
            "op_Addition",
            "op_Implicit",
        ]
    );
}

#[test]
fn an_accessor_with_a_body_is_a_method_under_its_property() {
    let compilation = compile(&["class C {
            int store;
            public int Named { get { return store; } set { store = value; } }
            public int Automatic { get; set; }
            public int Arrow => store;
            public int this[int i] { get { return i; } }
        }"]);
    // The accessors sit under the property, not under the type: C# forbids
    // calling `get_Named` by name, so nothing may find one by looking at `C`.
    assert_eq!(
        member_names(&compilation, "C"),
        vec!["store", "Named", "Automatic", "Arrow", "this[]", ".ctor"]
    );

    assert_eq!(
        member_names(&compilation, "C.Named"),
        vec!["get_Named", "set_Named"]
    );
    // A setter is given a `value` parameter nobody wrote.
    assert_eq!(
        member_names(&compilation, "C.Named.set_Named"),
        vec!["value"]
    );

    // An automatic property has no accessor bodies, so it has no accessor
    // symbols; an expression-bodied one *is* its getter.
    assert!(member_names(&compilation, "C.Automatic").is_empty());
    assert!(member_names(&compilation, "C.Arrow").is_empty());

    // An indexer's accessors are named after the type's default member, and
    // its arguments stay on the property where both accessors can see them.
    assert_eq!(
        member_names(&compilation, "C.this[]"),
        vec!["i", "get_Item"]
    );
}

#[test]
fn a_field_declaration_can_declare_several_fields() {
    let compilation = compile(&["class C { int a, b = 1, c; }"]);
    assert_eq!(
        member_names(&compilation, "C"),
        vec!["a", "b", "c", ".ctor"]
    );
    let symbols = compilation.symbols();
    assert!(
        symbols
            .get(find(&compilation, "C.b"))
            .as_field()
            .unwrap()
            .has_initializer
    );
    assert!(
        !symbols
            .get(find(&compilation, "C.a"))
            .as_field()
            .unwrap()
            .has_initializer
    );
}

#[test]
fn accessibility_defaults_follow_the_container() {
    let compilation = compile(&[
        "class C { int a; public int b; protected internal int c; private protected int d; }
         interface I { void M(); }
         class Outer { class Nested {} }",
    ]);
    let symbols = compilation.symbols();
    let access = |name: &str| symbols.get(find(&compilation, name)).accessibility;
    assert_eq!(access("C"), Accessibility::Internal);
    assert_eq!(access("C.a"), Accessibility::Private);
    assert_eq!(access("C.b"), Accessibility::Public);
    assert_eq!(access("C.c"), Accessibility::ProtectedOrInternal);
    assert_eq!(access("C.d"), Accessibility::ProtectedAndInternal);
    assert_eq!(access("I.M"), Accessibility::Public);
    assert_eq!(access("Outer.Nested"), Accessibility::Private);
}

#[test]
fn modifiers_are_kept() {
    let compilation =
        compile(&["abstract class C { public abstract void M(); static readonly int F = 1; }"]);
    let symbols = compilation.symbols();
    assert!(
        symbols
            .get(find(&compilation, "C"))
            .modifiers
            .contains(Modifiers::ABSTRACT)
    );
    assert!(
        symbols
            .get(find(&compilation, "C.M"))
            .modifiers
            .contains(Modifiers::ABSTRACT)
    );
    let field = symbols.get(find(&compilation, "C.F")).modifiers;
    assert!(field.contains(Modifiers::STATIC) && field.contains(Modifiers::READONLY));
}

#[test]
fn a_primary_constructor_is_a_constructor() {
    let compilation = compile(&["record Point(int X, int Y);"]);
    let symbols = compilation.symbols();
    let ctor = symbols.get(find(&compilation, "Point..ctor"));
    assert_eq!(
        ctor.as_method().unwrap().method_kind,
        MethodKind::Constructor
    );
    assert_eq!(ctor.as_method().unwrap().parameters.len(), 2);
    assert_eq!(symbols.get(ctor.members[0]).name, "X");
}

#[test]
fn parameters_remember_how_they_are_passed() {
    let compilation = compile(&[
        "class C { void M(int a, ref int b, out int c, in int d, params int[] e, int f = 1) {} }",
    ]);
    let symbols = compilation.symbols();
    let method = symbols.get(find(&compilation, "C.M"));
    let kinds: Vec<_> = method
        .as_method()
        .unwrap()
        .parameters
        .iter()
        .map(|id| {
            let parameter = symbols.get(*id).as_parameter().unwrap();
            (
                parameter.ref_kind,
                parameter.is_params,
                parameter.has_default,
            )
        })
        .collect();
    use rustlyn_semantics::RefKind;
    assert_eq!(
        kinds,
        vec![
            (RefKind::None, false, false),
            (RefKind::Ref, false, false),
            (RefKind::Out, false, false),
            (RefKind::In, false, false),
            (RefKind::None, true, false),
            (RefKind::None, false, true),
        ]
    );
}

#[test]
fn properties_remember_their_accessors() {
    let compilation = compile(&[
        "class C { int A { get; set; } int B { get; init; } int D => 1; int E { get {return 1;} } }",
    ]);
    let symbols = compilation.symbols();
    let property = |name: &str| {
        symbols
            .get(find(&compilation, name))
            .as_property()
            .unwrap()
            .clone()
    };
    assert!(property("C.A").has_get && property("C.A").has_set);
    assert!(property("C.B").has_init && !property("C.B").has_set);
    assert!(property("C.D").has_get && !property("C.D").has_set);
    assert!(property("C.E").has_get);
}

#[test]
fn enum_members_are_constants() {
    let compilation = compile(&["enum Color : byte { Red, Green = 2, Blue }"]);
    assert_eq!(
        member_names(&compilation, "Color"),
        vec!["Red", "Green", "Blue"]
    );
    let symbols = compilation.symbols();
    let red = symbols.get(find(&compilation, "Color.Red"));
    assert!(red.modifiers.contains(Modifiers::CONST));
    assert_eq!(red.accessibility, Accessibility::Public);
    assert!(
        symbols
            .get(find(&compilation, "Color"))
            .as_named_type()
            .unwrap()
            .enum_underlying
            .is_some()
    );
}

#[test]
fn a_delegate_carries_its_signature_on_invoke() {
    let compilation = compile(&["delegate int Transform<T>(T value, int scale);"]);
    let symbols = compilation.symbols();
    let invoke = symbols.get(find(&compilation, "Transform`1.Invoke"));
    assert_eq!(invoke.kind, SymbolKind::Method);
    assert_eq!(invoke.as_method().unwrap().parameters.len(), 2);
    assert!(invoke.as_method().unwrap().return_type.is_some());
}

#[test]
fn overloads_share_a_name() {
    let compilation = compile(&["class C { void M() {} void M(int x) {} void M(string s) {} }"]);
    let symbols = compilation.symbols();
    assert_eq!(symbols.lookup(find(&compilation, "C"), "M").len(), 3);
}

// -- the core library ------------------------------------------------------

#[test]
fn the_synthesised_core_library_provides_the_special_types() {
    let compilation = Compilation::from_source("class C {}");
    for special in SpecialType::ALL {
        assert!(
            compilation.special_type(*special).is_some(),
            "{} should exist",
            special.metadata_name()
        );
    }
    assert!(!compilation.has_errors(), "the core library should compile");
}

#[test]
fn types_can_be_found_by_metadata_name() {
    let compilation = Compilation::from_source("class C {}");
    assert!(compilation.type_by_metadata_name("System.String").is_some());
    assert!(
        compilation
            .type_by_metadata_name("System.Collections.Generic.List`1")
            .is_some()
    );
    assert!(
        compilation
            .type_by_metadata_name("System.Collections.Generic.List")
            .is_none(),
        "the arity is part of the name"
    );
    assert!(compilation.type_by_metadata_name("C").is_some());
    assert!(
        compilation
            .type_by_metadata_name("System.Nonesuch")
            .is_none()
    );
}

#[test]
fn source_diagnostics_leave_the_core_library_out() {
    let compilation = Compilation::from_source("class C {\n");
    assert!(!compilation.source_diagnostics().is_empty());
    assert!(
        compilation
            .source_diagnostics()
            .iter()
            .all(|entry| entry.tree > 0)
    );
}

#[test]
fn a_record_is_given_the_members_the_language_promises() {
    let compilation = compile(&["record Point(int X, int Y);"]);
    // The positional parameters become properties, and the rest is what makes
    // a record a record: value equality, a `ToString` that prints what it
    // holds, a `Deconstruct` that hands its parts back, and the `<Clone>$`
    // and copy constructor a `with` expression copies it through — in the
    // order Roslyn's `AddSynthesizedRecordMembersIfNecessary` adds them,
    // with the `EqualityContract`, `Equals(Point)` and `PrintMembers` the
    // others are written in terms of.
    assert_eq!(
        member_names(&compilation, "Point"),
        vec![
            ".ctor",
            "X",
            "Y",
            "Deconstruct",
            ".ctor",
            "<Clone>$",
            "EqualityContract",
            "Equals",
            "Equals",
            "GetHashCode",
            "op_Equality",
            "op_Inequality",
            "PrintMembers",
            "ToString",
        ]
    );
}

#[test]
fn a_record_struct_is_copied_without_a_clone() {
    let compilation = compile(&["record struct Point(int X, int Y);"]);
    let names = member_names(&compilation, "Point");
    assert!(!names.contains(&"<Clone>$".to_string()));
    assert_eq!(names.iter().filter(|name| *name == ".ctor").count(), 1);
}

#[test]
fn a_record_member_written_in_the_body_wins() {
    let compilation =
        compile(&["record Point(int X, int Y) { public int X { get { return 0; } } }"]);
    // Only one `X`: the source declared it, so the language does not.
    assert_eq!(
        member_names(&compilation, "Point")
            .into_iter()
            .filter(|name| name == "X")
            .count(),
        1
    );
}
