//! A call to something the code may not call. Roslyn looks a method's name
//! up among what is accessible before it counts arguments, so an
//! inaccessible overload beside an accessible one is not the one a call
//! names; a constructor is different, and one that only an inaccessible
//! overload takes is CS0122. Every code here is the one Roslyn reports, at
//! the place it reports it.

use rustlyn_semantics::Compilation;
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

/// Every error for a file, as `CS0000 'underlined'`, in the order of where
/// they are.
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

#[test]
fn a_constructor_the_code_may_not_call_is_cs0122() {
    let found = diagnose(
        r"
class Ct { Ct(int a) {} private Ct(int a, int b) {} }
class Ct2 { Ct2(int a) {} }
class Ct3 { private Ct3() {} public Ct3(int a) {} }
class Ct4 { protected Ct4(int a) {} }
class Outside
{
    void M()
    {
        var b = new Ct(1);
        var c = new Ct2(1);
        var d = new Ct3();
        var e = new Ct4(1);
        Ct f = new(1, 2);
    }
}
",
    );
    assert_eq!(
        found,
        [
            "CS0122 'Ct'",
            "CS0122 'Ct2'",
            "CS0122 'Ct3'",
            "CS0122 'Ct4'",
            "CS0122 'new'",
        ]
    );
}

/// The arguments still have to fit: what no constructor takes, hidden or
/// not, is reported as before.
#[test]
fn a_hidden_constructor_that_does_not_fit_is_not_the_one_named() {
    let found = diagnose(
        r#"
class Ct3 { private Ct3() {} public Ct3(int a) {} }
class Outside { void M() { var f = new Ct3("s"); } }
"#,
    );
    assert_eq!(found, ["CS1503 '\"s\"'"]);
}

#[test]
fn a_constructor_reached_from_where_it_may_be_is_quiet() {
    let found = diagnose(
        r#"
using System;
using System.Collections.Generic;
class Single
{
    private Single() { }
    public static Single Make() => new Single();
    class In { Single s = new Single(); }
    static readonly Single One = new();
    Func<Single> f = () => new Single();
}
class Pr { protected Pr() { } protected Pr(int a) { } }
class Dr : Pr { Dr() : base(1) { } static Pr Mk() => new Dr(); class N { Dr d = new Dr(); } }
class G<T>
{
    private G(T t) { }
    public static G<T> Of(T t) => new G<T>(t);
    public static G<int> I() => new G<int>(1);
}
partial class Pa { private Pa(int x) { } }
partial class Pa { static Pa Mk() => new Pa(1) { }; }
class Ov { private Ov(int a) { } public Ov(long a) { } public Ov(object o) { } }
abstract class Ab { protected Ab() { } }
class AbD : Ab { }
record R(int X) { private R(string s) : this(1) { } public static R P(string s) => new R(s); }
record struct RS(int X);
struct St { private St(int a) { } public static St Mk() => new St(1); }
class Outside
{
    void M()
    {
        var a = new Ov(1);
        var b = new Ov("s");
        var c = new AbD();
        var r = new R(1) with { X = 2 };
        var s = new St();
        var rs = new RS(1) with { X = 3 };
        var l = new List<int> { 1 };
        var e = new Exception("x");
    }
}
"#,
    );
    assert!(found.is_empty(), "expected nothing, found {found:#?}");
}

/// One method that may be called is the one the call is judged against;
/// only a name with none is CS0122, and then whatever it is given.
#[test]
fn a_method_name_is_inaccessible_only_where_none_of_its_methods_may_be_called() {
    let found = diagnose(
        r#"
class Base { public void S(int a) {} void S(int a, int b) {} }
class Base2 { private void M(int a, int b) {} }
class Derived2 : Base2 { public void M(int a) {} }
class Other
{
    void X(int a, int b) {}
    private void Y(int a) {}
    private static void Z() {}
    void W(string s) {}
    public void W(int a, int b) {}
}
class Stranger
{
    void M(Derived2 d, Other o)
    {
        new Base().S(1, 2);
        d.M(1, 2);
        o.X(1);
        o.X(1, 2);
        o.Y(1);
        o.Y();
        o.Y("s");
        Other.Z();
        Other.Z(1);
        o.W("s");
        o.W(1);
    }
}
"#,
    );
    assert_eq!(
        found,
        [
            "CS1501 'S'",
            "CS1501 'M'",
            "CS0122 'X'",
            "CS0122 'X'",
            "CS0122 'Y'",
            "CS0122 'Y'",
            "CS0122 'Y'",
            "CS0122 'Z'",
            "CS0122 'Z'",
            "CS7036 'W'",
            "CS7036 'W'",
        ]
    );
}
