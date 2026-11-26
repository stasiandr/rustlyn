//! CS0121: a call two overloads take equally well, in the shapes that went
//! unreported while only plain methods were judged — constructors, extension
//! methods, indexers, optional parameters, `params`, generic methods and
//! nullable parameters — each beside the near-identical calls that are fine
//! and must stay quiet. Every case here was put to Roslyn.

use rustlyn_semantics::Compilation;
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

/// Every diagnostic for a file, as `CS0000 'underlined': message`, in the
/// order of where they are.
fn diagnose(source: &str) -> Vec<String> {
    let compilation = Compilation::create(vec![parse(SourceText::new("Program.cs", source))]);
    let mut found: Vec<_> = compilation
        .source_diagnostics()
        .into_iter()
        .map(|entry| entry.diagnostic.clone())
        .chain(
            compilation
                .semantic_diagnostics()
                .into_iter()
                .map(|entry| entry.diagnostic),
        )
        .collect();
    found.sort_by_key(|diagnostic| (diagnostic.span().start(), diagnostic.code()));
    found
        .iter()
        .map(|diagnostic| {
            let span = diagnostic.span();
            format!(
                "{} '{}': {}",
                diagnostic.code(),
                &source[span.start() as usize..span.end() as usize],
                diagnostic.message()
            )
        })
        .collect()
}

/// Just the codes.
fn codes(source: &str) -> Vec<String> {
    diagnose(source)
        .into_iter()
        .map(|line| line[..6].to_string())
        .collect()
}

/// The errors among `wanted` that a file gets, whatever else it is told.
fn only(source: &str, wanted: &[&str]) -> Vec<String> {
    codes(source)
        .into_iter()
        .filter(|code| wanted.contains(&code.as_str()))
        .collect()
}

/// How many calls in `source` are reported ambiguous.
fn ambiguous(source: &str) -> usize {
    only(source, &["CS0121"]).len()
}

// MARK: - constructors

/// Types to construct, and a method whose parameters are the arguments.
fn constructed(body: &str) -> String {
    format!(
        "class Animal {{ }} class Dog : Animal {{ }}
         class A {{ public A(int a, long b) {{ }} public A(long a, int b) {{ }} }}
         class A2 {{ public A2(int a, long b) {{ }} public A2(long a, int b) {{ }} public A2(int a, int b) {{ }} }}
         class A3 {{ public A3(Animal a, Dog b) {{ }} public A3(Dog a, Animal b) {{ }} }}
         struct S {{ public S(int a, long b) {{ }} public S(long a, int b) {{ }} }}
         class E {{ public E(int? a, long b) {{ }} public E(long a, int? b) {{ }} }}
         class F {{ public F(int a, long b = 0) {{ }} public F(long a, int b) {{ }} }}
         class G {{ public G(int a) {{ }} public G(long a) {{ }} public G(params int[] x) {{ }} }}
         class Gn<T> {{ public Gn(T a, long b) {{ }} public Gn(long a, int b) {{ }} }}
         class C {{ void T(int i, long l, Dog d) {{ {body} }} }}"
    )
}

#[test]
fn a_constructor_call_two_constructors_take_equally_well_is_cs0121() {
    assert_eq!(
        diagnose(&constructed("new A(i, i);")),
        [
            "CS0121 'A': The call is ambiguous between the following methods or properties: 'A.A(int, long)' and 'A.A(long, int)'"
        ]
    );
    for call in [
        "new A(1, 1);",
        "var a = new A(i, i) { };",
        "A a = new(i, i);",
        "new A3(d, d);",
        "new S(i, i);",
        "new E(i, i);",
        "new Gn<int>(i, i);",
    ] {
        assert_eq!(ambiguous(&constructed(call)), 1, "{call}");
    }
}

#[test]
fn an_initializer_that_could_chain_to_two_constructors_is_cs0121_on_its_keyword() {
    let source = "class Base { public Base(int a, long b) { } public Base(long a, int b) { } }
         class Chain : Base {
             public Chain(string s) : base(1, 1) { }
             public Chain(char c) : this(1, 1) { }
             public Chain(int a, long b) : base(1L, 1) { }
             public Chain(long a, int b) : base(1L, 1) { }
             // Each is better for one of the two calls, and the call that names
             // one of them exactly is the one made.
             public Chain(int a) : this(a, 1L) { }
             public Chain(long a) : base(a, 1) { }
         }";
    let found = diagnose(source);
    assert_eq!(
        found.iter().map(|line| &line[..13]).collect::<Vec<_>>(),
        ["CS0121 'base'", "CS0121 'this'"],
        "{found:#?}"
    );
}

#[test]
fn a_constructor_call_one_constructor_takes_best_is_not_cs0121() {
    for call in [
        "new A(i, l); new A(l, i);",
        // A third beats both.
        "new A2(i, i); new A2(1, 1);",
        // The one that is not generic wins, and the number of defaults.
        "new Gn<int>(l, i);",
        "new G(i); new G(i, i); new G(l);",
        "new E(i, l); new E(l, i);",
        "new F(i, l);",
        "new S(i, l);",
        "new A3(d, new Animal());",
    ] {
        assert_eq!(ambiguous(&constructed(call)), 0, "{call}");
    }
}

// MARK: - extension methods

/// Extension methods in two static classes, both in scope, and in a third
/// that is nearer.
fn extended(body: &str) -> String {
    format!(
        "namespace NsA {{
             public class Animal {{ }} public class Dog : Animal {{ }}
             public static class ExtA {{
                 public static void Ext(this int x) {{ }}
                 public static void Two(this string s, int a) {{ }}
                 public static void Gen<T>(this T x) {{ }}
                 public static void Spec(this object x) {{ }}
                 public static void Cross(this int x, int a, long b) {{ }}
                 public static void Cross(this int x, long a, int b) {{ }}
                 public static void Opt(this int x, int a = 0) {{ }}
                 public static void Par(this int x, params int[] a) {{ }}
                 public static void Recv(this long x) {{ }}
                 public static void Recv2(this long x) {{ }}
                 public static void Cls(this Animal a) {{ }}
                 public static void Obj(this object a) {{ }}
                 public static void Only(this int x) {{ }}
                 public static void Gn2<T>(this T x) where T : class {{ }}
             }}
         }}
         namespace NsB {{
             public static class ExtB {{
                 public static void Ext(this int x) {{ }}
                 public static void Two(this string s, long a) {{ }}
                 public static void Gen<T>(this T x) {{ }}
                 public static void Spec(this string x) {{ }}
                 public static void Opt(this int x, int a = 0) {{ }}
                 public static void Par(this int x, params int[] a) {{ }}
                 public static void Recv(this int x) {{ }}
                 public static void Recv2(this long x) {{ }}
                 public static void Cls(this NsA.Dog a) {{ }}
                 public static void Obj(this object a) {{ }}
                 public static void Gn2<T>(this T x) where T : struct {{ }}
             }}
         }}
         namespace Elsewhere {{
             static class Near {{ public static void Ext(this int x) {{ }} }}
         }}
         namespace Nested {{
             using NsA; using NsB;
             class Near {{ }}
             static class NearExt {{ public static void Ext(this int x) {{ }} }}
             class D {{ void T(int i) {{ i.Ext(); }} }}
         }}
         namespace Main {{
             using NsA; using NsB;
             class C {{ void T(int i, long l, string s, Animal an, Dog dg, object o) {{ {body} }} }}
         }}"
    )
    .replace("Animal an", "NsA.Animal an")
    .replace("Dog dg", "NsA.Dog dg")
}

#[test]
fn an_extension_method_two_classes_in_scope_both_declare_is_cs0121() {
    let found = diagnose(&extended("i.Ext();"));
    assert_eq!(
        found,
        [
            "CS0121 'Ext': The call is ambiguous between the following methods or properties: 'NsA.ExtA.Ext(int)' and 'NsB.ExtB.Ext(int)'"
        ]
    );
    for call in [
        // Generic on both sides, declared alike.
        "i.Gen();",
        "an.Obj();",
        // The same by their parameters, one that is better nowhere.
        "l.Recv2();",
        // Crossed within one class.
        "i.Cross(i, i);",
        // A default or an expanded `params` that is filled in on both.
        "i.Opt(1);",
        "i.Par(1, 2);",
    ] {
        assert_eq!(ambiguous(&extended(call)), 1, "{call}");
    }
}

#[test]
fn an_extension_method_that_one_class_does_better_is_not_cs0121() {
    for call in [
        // The more specific receiver, and the one that takes an `int`.
        "s.Two(1);",
        "dg.Cls(); an.Cls();",
        "s.Spec(); i.Spec();",
        // `5.Recv()` reaches only the `int` one: a numeric conversion does
        // not make a receiver.
        "i.Recv(); l.Recv();",
        "i.Cross(i, l); i.Cross(l, i);",
        // One is not applicable to the type, by its constraint.
        "an.Gn2();",
        "i.Only();",
    ] {
        assert_eq!(ambiguous(&extended(call)), 0, "{call}");
    }
}

#[test]
fn an_extension_method_in_a_nearer_namespace_hides_the_ones_beyond() {
    // `NearExt` is declared in `Nested`, whose `using`s are looked at after
    // the namespace's own types: it alone is a candidate there.
    assert_eq!(ambiguous(&extended("")), 0);
}

// MARK: - indexers

/// Types with indexers, and a method whose parameters are the arguments.
fn indexed(body: &str) -> String {
    format!(
        "class Animal {{ }} class Dog : Animal {{ }}
         class X {{ public int this[int a, long b] {{ get => 0; set {{ }} }} public int this[long a, int b] {{ get => 0; set {{ }} }} }}
         class X2 {{ public int this[int a, long b] => 0; public int this[long a, int b] => 0; public int this[int a, int b] => 0; }}
         class X3 {{ public int this[Animal a, Dog b] => 0; public int this[Dog a, Animal b] => 0; }}
         class X4 {{ public int this[int a] => 0; public int this[long a] => 0; public int this[string s] => 0; }}
         class X5 {{ public int this[int? a, long b] => 0; public int this[long a, int? b] => 0; }}
         class X6 {{ public int this[int a, long b = 0] => 0; public int this[long a, int b] => 0; }}
         class X7 {{ public int this[int a, params long[] b] => 0; public int this[long a, int b] => 0; }}
         class B {{ public int this[int a, long b] => 0; }}
         class D : B {{ public int this[long a, int b] => 0; }}
         class Y {{ void T(X x, X2 x2, X3 x3, X4 x4, X5 x5, X6 x6, X7 x7, D d, int i, long l, Dog dg, string s) {{ int a; {body} }} }}"
    )
}

#[test]
fn an_index_two_indexers_take_equally_well_is_cs0121() {
    assert_eq!(
        diagnose(&indexed("a = x[i, i];")),
        [
            "CS0121 'x[i, i]': The call is ambiguous between the following methods or properties: 'X.this[int, long]' and 'X.this[long, int]'"
        ]
    );
    for access in [
        // Written to, and read and written.
        "x[i, i] = 1;",
        "x[i, i] += 1;",
        "a = x3[dg, dg];",
        "a = x5[i, i];",
        "a = x6[i, i];",
        "a = x7[i, i];",
        "a = x?[i, i] ?? 0;",
    ] {
        assert_eq!(ambiguous(&indexed(access)), 1, "{access}");
    }
}

#[test]
fn an_index_one_indexer_takes_best_is_not_cs0121() {
    for access in [
        "a = x[i, l]; a = x[l, i];",
        "a = x2[i, i]; a = x2[1, 1];",
        "a = x4[i]; a = x4[l]; a = x4[s]; a = x4[1];",
        // An indexer of a derived class is the only one looked at.
        "a = d[l, i];",
    ] {
        assert_eq!(ambiguous(&indexed(access)), 0, "{access}");
    }
}

// MARK: - optional parameters, `params`, generic methods and nullable ones

/// Overloads to call, and a method whose parameters are the arguments.
fn shaped(body: &str) -> String {
    format!(
        "class Animal {{ }} class Dog : Animal {{ }}
         interface IA {{ }} interface IB {{ }} class AB : IA, IB {{ }}
         class C {{
             static void Z(int? a, long b) {{ }}
             static void Z(long a, int? b) {{ }}
             static void Z2(int? a, long b) {{ }}
             static void Z2(long a, int? b) {{ }}
             static void Z2(int a, int b) {{ }}
             static void Z3(int? a, long? b) {{ }}
             static void Z3(long? a, int? b) {{ }}
             static void Z4(int? a, uint b) {{ }}
             static void Z4(uint a, int? b) {{ }}
             static void Z5(int? a, long b) {{ }}
             static void Z5(long a, int b) {{ }}
             static void Z6(char? a, long b) {{ }}
             static void Z6(long a, char? b) {{ }}
             static void O1(int a, long b = 0) {{ }}
             static void O1(long a, int b) {{ }}
             static void O2(int a, long b, int c = 0) {{ }}
             static void O2(long a, int b) {{ }}
             static void O3(int a, long b) {{ }}
             static void O3(long a, int b, int c = 0) {{ }}
             static void P1(int a, long b) {{ }}
             static void P1(long a, int b) {{ }}
             static void P1(params long[] x) {{ }}
             static void P2(int a, long b) {{ }}
             static void P2(long a, int b) {{ }}
             static void P2(params int[] x) {{ }}
             static void P3(int a, params long[] x) {{ }}
             static void P3(long a, int b) {{ }}
             static void P4(int a, int b, params int[] x) {{ }}
             static void P4(long a, int b) {{ }}
             static void P5(int a, long b, params int[] x) {{ }}
             static void P5(long a, int b, params int[] x) {{ }}
             static void P6(IA a) {{ }}
             static void P6(params IB[] b) {{ }}
             static void P7(int[] a, int b) {{ }}
             static void P7(params long[] a) {{ }}
             static void G1<T>(T a, long b) {{ }}
             static void G1(long a, int b) {{ }}
             static void G2<T>(T a, long b) {{ }}
             static void G2<T>(long a, T b) {{ }}
             static void G3<T>(T a, long b) {{ }}
             static void G3<T>(long a, T b) {{ }}
             static void G3(int a, int b) {{ }}
             static void G4<T>(T a, long b) {{ }}
             static void G4(int a, long b) {{ }}
             static void G5<T>(T a, Animal b) {{ }}
             static void G5<T>(Animal a, T b) {{ }}
             static void G6<T>(T a, long b) where T : class {{ }}
             static void G6(long a, int b) {{ }}
             static void G7<T>(T a, T b) {{ }}
             static void G7(long a, int b) {{ }}
             static void G8<T>(T a, int b) {{ }}
             static void G8(int a, int b) {{ }}
             void Test(int i, long l, short sh, char ch, uint u, int? ni, Dog dg, AB ab) {{ {body} }}
         }}"
    )
}

#[test]
fn a_call_crossed_over_nullable_parameters_is_cs0121() {
    for call in [
        "Z(i, i);",
        "Z(sh, sh);",
        "Z(1, 1);",
        "Z3(i, i);",
        "Z6(ch, ch);",
    ] {
        assert_eq!(ambiguous(&shaped(call)), 1, "{call}");
    }
}

#[test]
fn a_call_one_nullable_overload_takes_best_is_not_cs0121() {
    for call in [
        "Z(i, l); Z(l, i); Z(ni, l); Z(l, ni);",
        // A third is the better of both.
        "Z2(i, i);",
        // Only one reaches: `int` is better for `int?`.
        "Z5(i, i);",
        // An unsigned type is where the rule that prefers a signed target
        // over an unsigned one comes in, and nothing is said.
        "Z4(i, u); Z4(u, i);",
    ] {
        assert_eq!(ambiguous(&shaped(call)), 0, "{call}");
    }
}

#[test]
fn a_call_crossed_with_a_parameter_that_has_a_default_is_cs0121_where_it_is_given() {
    assert_eq!(ambiguous(&shaped("O1(i, i);")), 1);
    // A default taken that the other does not need is Roslyn's to settle,
    // and it prefers the call that fills every parameter.
    for call in ["O2(i, i);", "O3(i, i);", "O1(i, l);", "O1(i);"] {
        assert_eq!(ambiguous(&shaped(call)), 0, "{call}");
    }
}

#[test]
fn a_call_crossed_with_a_params_method_is_cs0121() {
    for call in [
        // The expanded form is worse than both, and is no help.
        "P1(i, i);",
        // The expanded form is one of the crossed ones.
        "P3(i, i);",
        "P5(i, i, i);",
        // Neither is better, and a `params` makes no difference to that.
        "P6(ab);",
    ] {
        assert_eq!(ambiguous(&shaped(call)), 1, "{call}");
    }
}

#[test]
fn a_call_a_params_method_takes_best_is_not_cs0121() {
    for call in [
        // The expanded form is better at both arguments.
        "P2(i, i);",
        "P4(i, i);",
        "P7(new int[0], i);",
    ] {
        assert_eq!(ambiguous(&shaped(call)), 0, "{call}");
    }
}

#[test]
fn a_call_crossed_with_a_generic_method_is_cs0121() {
    for call in [
        // What `T` is the argument's own type.
        "G1(i, i);",
        "G2(i, i);",
        "G5(dg, dg);",
    ] {
        assert_eq!(ambiguous(&shaped(call)), 1, "{call}");
    }
}

#[test]
fn a_call_a_generic_method_does_not_cross_is_not_cs0121() {
    for call in [
        "G1(l, i);",
        // A third overload is better than both.
        "G3(i, i);",
        // `int` is `T` and the method that is not generic is better.
        "G4(i, l); G8(i, i);",
        // `T` cannot be an `int`.
        "G6(i, i);",
        // Equal where `T` is `int`, and Roslyn breaks the tie.
        "G7(l, i);",
    ] {
        assert_eq!(ambiguous(&shaped(call)), 0, "{call}");
    }
}
