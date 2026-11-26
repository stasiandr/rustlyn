//! A nested type named from code that may not name it is CS0122, wherever
//! the name is written; and each way of naming one that is allowed — from
//! inside its owner, from a type derived from it, through inheritance —
//! stays quiet. A false error on code Roslyn accepts is the worse mistake,
//! so every error here is placed where Roslyn puts it, at the type's own
//! name.

use rustlyn_semantics::Compilation;
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

/// Every diagnostic for a file, as `CS0000 'underlined'`, in the order of
/// where they are.
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
        .filter(rustlyn_diagnostics::Diagnostic::is_error)
        .collect();
    found.sort_by_key(|diagnostic| (diagnostic.span().start(), diagnostic.code()));
    found
        .iter()
        .map(|diagnostic| {
            let span = diagnostic.span();
            format!(
                "{} '{}'",
                diagnostic.code(),
                &source[span.start() as usize..span.end() as usize]
            )
        })
        .collect()
}

fn assert_clean(source: &str) {
    let found = diagnose(source);
    assert!(found.is_empty(), "expected nothing, found {found:#?}");
}

/// A class with one nested type of each accessibility, then `rest`.
fn with_owner(rest: &str) -> String {
    format!(
        "using System;\nusing System.Collections.Generic;\n\
         public class Outer {{\n\
             private class Priv {{ public class Deep {{ }} }}\n\
             protected class Prot {{ public class Deep {{ }} }}\n\
             private protected class PrivProt {{ }}\n\
             protected internal class ProtInt {{ }}\n\
             internal class Intern {{ }}\n\
             public class Pub {{ }}\n\
         }}\n{rest}"
    )
}

#[test]
fn a_private_or_protected_nested_type_named_from_a_body_is_cs0122() {
    let source = with_owner(
        "class Stranger {
    void M(object o) {
        var a = new Outer.Priv();
        Outer.Priv b = null;
        var c = (Outer.Priv)o;
        var t = typeof(Outer.Priv);
        var l = new List<Outer.Priv>();
        bool z = o is Outer.Priv;
        Outer.Priv.Deep q = null;
        var d = new Outer.Prot.Deep();
        Outer.PrivProt e = null;
        foreach (Outer.Prot x in new Outer.Prot[0]) { }
        var ok1 = new Outer.ProtInt();
        var ok2 = new Outer.Intern();
        var ok3 = new Outer.Pub();
    }
}",
    );
    assert_eq!(
        diagnose(&source),
        [
            "CS0122 'Priv'",
            "CS0122 'Priv'",
            "CS0122 'Priv'",
            "CS0122 'Priv'",
            "CS0122 'Priv'",
            "CS0122 'Priv'",
            "CS0122 'Priv'",
            "CS0122 'Prot'",
            "CS0122 'PrivProt'",
            "CS0122 'Prot'",
            "CS0122 'Prot'",
        ]
    );
}

#[test]
fn an_inaccessible_nested_type_named_in_a_declaration_is_cs0122() {
    let source = with_owner(
        "class Stranger {
    Outer.Priv field;
    Outer.Priv M(Outer.Priv p) => p;
    List<Outer.Prot> list;
    event Action<Outer.Priv> E;
    Outer.PrivProt Prop { get; set; }
    Outer.ProtInt fine;
}
class FromPrivate : Outer.Priv { }
class FromProtected : Outer.Prot { }
class InTheList : List<Outer.Priv> { }",
    );
    assert_eq!(
        diagnose(&source),
        [
            "CS0122 'Priv'",
            "CS0122 'Priv'",
            "CS0122 'Priv'",
            "CS0122 'Prot'",
            "CS0122 'Priv'",
            "CS0122 'PrivProt'",
            "CS0122 'Priv'",
            "CS0122 'Prot'",
            "CS0122 'Priv'",
        ]
    );
}

#[test]
fn an_alias_of_an_inaccessible_type_is_one_error_at_the_alias() {
    let source = "using A = Outer.Priv;
public class Outer { private class Priv { } }
class User { A f; A g; void M() { A a = null; } }";
    assert_eq!(diagnose(source), ["CS0122 'Priv'"]);
}

#[test]
fn a_nested_type_inside_its_owner_or_what_is_nested_in_it_is_named_freely() {
    assert_clean(
        "using System;
using System.Collections.Generic;
public partial class Outer {
    private class Priv { public static int S; public class Deep { } }
    protected class Prot { public static int S; }
    private protected class PP { }
    private static readonly Outer.Priv sf = new Outer.Priv();
    private Outer.Priv inst = new Outer.Priv();
    Outer.Priv PropE => new Outer.Priv();
    int Z = Outer.Priv.S;
    public Outer() : this(new Outer.Priv()) { }
    private Outer(Outer.Priv p) { }
    public struct StructIn { Outer.Priv p; void M() { var x = new Outer.Priv(); } }
    public record RecIn(int A) { void M() { var x = new Outer.Priv(); Outer.Prot y; } }
    private delegate void Dg(Outer.Priv p);
    class Inner { void M() { var a = new Outer.Priv(); Outer.Prot b; var c = new Outer.Priv.Deep(); } }
    public static int Q() { Func<Outer.Priv> f = () => new Outer.Priv(); Outer.Priv local() => new Outer.Priv(); return Outer.Priv.S; }
    public static void Gn() { var l = new Dictionary<Outer.Priv, List<Outer.Prot>>(); (Outer.Priv, Outer.Prot) t = default; var n = typeof(Outer.Priv[]); }
    /// <see cref=\"Outer.Priv\"/>
    void Doc() { }
}
public partial class Outer { class MoreOfIt { Outer.Priv p; } }
class Self : List<Self.Inn> { private class Inn { } }
class Self2 { Self2.Inn f; private class Inn { } class Deep { Self2.Inn g; } }
class Self3 : IEquatable<Self3.Key> { private struct Key { } public bool Equals(Key k) => true; }",
    );
}

#[test]
fn a_protected_nested_type_is_named_freely_from_what_derives_from_its_owner() {
    assert_clean(&with_owner(
        "class Der : Outer {
    Outer.Prot a; Der.Prot b; Prot c; Outer.Prot.Deep d; Outer.PrivProt e; Outer.ProtInt f;
    List<Outer.Prot> list; Outer.Prot[] arr;
    Outer.Prot M(Outer.Prot p) => p;
    event Action<Outer.Prot> Ev;
    class Nested : Outer.Prot { Outer.Prot x; }
    class Nested2 : List<Outer.Prot> { }
    class Nested3 : Prot { }
    void N(object o) {
        var a = new Outer.Prot(); var b = new Der.Prot(); var c = new Prot(); var d = new Outer.Prot.Deep();
        var g = typeof(Outer.Prot); var h = (Outer.Prot)o; bool z = o is Outer.Prot; var i = new List<Outer.Prot>();
        var nn = nameof(Outer.Prot);
        Action act = () => { var w = new Outer.Prot(); };
        void Local() { var w = new Outer.PrivProt(); }
    }
}
class Der2 : Der { Outer.Prot a; Der2.Prot b; void N() { var a = new Outer.Prot(); var b = new Der.Prot(); } class In { void Q() { var a = new Outer.Prot(); } } }
class Out { class Der6 : Outer { void N() { var a = new Outer.Prot(); } } }
class Der7 : Outer { class A { class B { void N() { var a = new Outer.Prot(); var b = new Der7.Prot(); } } } }
partial class P1 : Outer { partial class In { void M() { var a = new Outer.Prot(); } } }
partial class P1 { partial class In { Outer.Prot f; } }",
    ));
}

#[test]
fn nested_types_of_generic_owners_follow_the_same_rule() {
    assert_clean(
        "using System;
public class Gen<T> {
    protected class In { public T V; }
    private class Pv { }
    class Z { Gen<int>.Pv f; Gen<T>.In g; }
    public static void M() { var a = new Gen<T>.In(); var b = new Gen<int>.In(); var c = new Gen<int>.Pv(); }
}
public class GenD : Gen<string> {
    void N() { var a = new Gen<string>.In(); var b = new In(); var c = new GenD.In(); Gen<string>.In d; Gen<int>.In e; }
}
public class GenD2<U> : Gen<U> {
    void N() { var a = new Gen<U>.In(); var b = new GenD2<U>.In(); var c = new GenD2<int>.In(); }
    class Q { void R() { var a = new Gen<U>.In(); var b = new GenD2<U>.In(); } }
}",
    );
    assert_eq!(
        diagnose(
            "public class Gen<T> { protected class In { } private class Pv { } }
class Stranger { void M() { var a = new Gen<int>.In(); var b = new Gen<int>.Pv(); } }"
        ),
        ["CS0122 'In'", "CS0122 'Pv'"]
    );
}

#[test]
fn a_base_list_does_not_make_its_type_derived_from_what_it_names_beside() {
    // `C : Outer, I<Outer.Prot>` is an error in Roslyn: the base list is
    // read before C is anyone's derived type.
    let source = with_owner(
        "interface IFoo<T> { }
class C : Outer, IFoo<Outer.Prot> { }
class D : Outer { class N : IFoo<Outer.Prot> { } }",
    );
    assert_eq!(diagnose(&source), ["CS0122 'Prot'"]);
}
