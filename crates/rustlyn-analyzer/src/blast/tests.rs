//! What a change reaches through the constructs of the language: a caller
//! that writes no name of what it runs is a caller all the same, and a name
//! that does not run what it names is not. Each case is by construction:
//! the member named in the comment is the one C# runs there.

use super::changes::{How, Touched, changes};
use super::diff::parse;
use super::testing::{Project, patch};
use super::walk::{Impact, Limits, Relation, walk};

/// Every member below is on a line of its own, and each body holds `/*1*/`,
/// which the change turns into `/*2*/`: every member changes, and the walk
/// says who calls each.
const LIB: &str = r#"using System;
using System.Collections.Generic;
using System.Threading.Tasks;

public class Money
{
    public int V;
    public Money() { /*1*/ }
    public Money(int v) { /*1*/ V = v; }
    public int this[int i] { get { /*1*/ return V + i; } set { /*1*/ V = value; } }
    public static Money operator +(Money a, Money b) { /*1*/ return a; }
    public static Money operator -(Money a) { /*1*/ return a; }
    public static Money operator &(Money a, Money b) { /*1*/ return a; }
    public static bool operator ==(Money a, Money b) { /*1*/ return true; }
    public static bool operator !=(Money a, Money b) { /*1*/ return false; }
    public static Money operator ++(Money a) { /*1*/ return a; }
    public static bool operator true(Money a) { /*1*/ return true; }
    public static bool operator false(Money a) { /*1*/ return false; }
    public static implicit operator int(Money m) { /*1*/ return m.V; }
    public static explicit operator Money(int v) { /*1*/ return new Money(v); }
    public override bool Equals(object o) { /*1*/ return true; }
    public override int GetHashCode() { /*1*/ return 1; }
    public override string ToString() { /*1*/ return "m"; }
    public int P { get { /*1*/ return V; } set { /*1*/ V = value; } }
    public int Compute() { /*1*/ return V; }
    public void Deconstruct(out int a, out int b) { /*1*/ a = 1; b = 2; }
}

public class Other
{
    public static Other operator +(Other a, Other b) { /*1*/ return a; }
    public static implicit operator int(Other o) { /*1*/ return 0; }
    public override string ToString() { /*1*/ return "o"; }
    public int Compute() { /*1*/ return 0; }
}

public class Plain
{
    public override string ToString() { /*1*/ return "p"; }
}

public class Bag : IDisposable
{
    public void Dispose() { /*1*/ }
    public void Add(int v) { /*1*/ }
    public Bag.Walker GetEnumerator() { /*1*/ return new Walker(); }
    public class Walker : IDisposable
    {
        public bool MoveNext() { /*1*/ return false; }
        public int Current { get { /*1*/ return 0; } }
        public void Dispose() { /*1*/ }
    }
}

public class Later : IAsyncDisposable
{
    public ValueTask DisposeAsync() { /*1*/ return default; }
}

public class Wait
{
    public Wait.Awaiter GetAwaiter() { /*1*/ return new Awaiter(); }
    public class Awaiter : System.Runtime.CompilerServices.INotifyCompletion
    {
        public bool IsCompleted { get { /*1*/ return true; } }
        public int GetResult() { /*1*/ return 1; }
        public void OnCompleted(Action continuation) { /*1*/ }
    }
}

public class Q
{
    public Q Select(Func<int, int> f) { /*1*/ return this; }
    public Q Where(Func<int, bool> f) { /*1*/ return this; }
}

public class Items
{
    public int Length { get { /*1*/ return 2; } }
    public int this[int i] { get { /*1*/ return i; } }
}

public record Rec
{
    public int X { get; init; }
    public Rec() { /*1*/ }
    protected Rec(Rec original) { /*1*/ X = original.X; }
}

public class MyAttribute : Attribute
{
    public MyAttribute(int v) { /*1*/ }
    public string Name { get { /*1*/ return ""; } set { /*1*/ } }
}

public class Events
{
    public event Action Fired;
    public void Handler() { /*1*/ }
}
"#;

const USE: &str = r#"using System;
using System.Threading.Tasks;

public class Use
{
    public Money NewTarget() { Money m = new(); return m; }
    public Money NewNamed() { return new Money(); }
    public Money NewInt() { Money m = new(5); return m; }
    public int IndexRead(Money m) { return m[3]; }
    public void IndexWrite(Money m) { m[3] = 1; }
    public void IndexBoth(Money m) { m[3] += 1; }
    public Money Add(Money a, Money b) { return a + b; }
    public Money AddAssign(Money a, Money b) { a += b; return a; }
    public Other AddOther(Other a, Other b) { return a + b; }
    public Money Neg(Money a) { return -a; }
    public bool Eq(Money a, Money b) { return a == b; }
    public bool Ne(Money a, Money b) { return a != b; }
    public Money Inc(Money a) { a++; return a; }
    public int IfTrue(Money a) { if (a) { return 1; } return 0; }
    public Money AndAlso(Money a, Money b) { return a && b; }
    public int ToInt(Money m) { int i = m; return i; }
    public int Cast(Money m) { return (int)m; }
    public int OtherToInt(Other o) { int i = o; return i; }
    public Money FromInt(int i) { return (Money)i; }
    public string Interp(Money m) { return $"{m}"; }
    public string Concat(Money m) { return "a" + m; }
    public string Named(Money m) { return m.ToString(); }
    public string AsObject(Money m) { object o = m; return $"{o}"; }
    public string OtherInterp(Other o) { return $"{o}"; }
    public void WritePlain(Plain p) { Console.WriteLine(p); }
    public void UsingStmt(Bag b) { using (b) { } }
    public void UsingDecl() { using var b = new Bag(); }
    public async Task AwaitUsing(Later l) { await using (l) { } }
    public void Each(Bag b) { foreach (var x in b) { } }
    public Bag Init() { return new Bag { 1, 2 }; }
    public Money Props() { return new Money { P = 4 }; }
    public void SetP(Money m) { m.P = 4; }
    public int GetP(Money m) { return m.P; }
    public int Decon(Money m) { var (a, b) = m; return a + b; }
    public bool PatternDecon(Money m) { return m is (1, _); }
    public async Task<int> Await(Wait w) { return await w; }
    public bool ListPattern(Items i) { return i is [1, ..]; }
    public Q Query(Q q) { return from x in q where x > 1 select x + 1; }
    public Rec With(Rec r) { return r with { X = 2 }; }
    [My(3)] public int Marked;
    public Func<int> Group(Money m) { Func<int> f = m.Compute; return f; }
    public string Nameof() { return nameof(Money.Compute); }
    public Type Typeof() { return typeof(Money); }
    /// <see cref="Money.Compute"/>
    public int Doc() { return 0; }
    public void Subscribe(Events e) { e.Fired += e.Handler; }
}
"#;

/// The walk of a change that turns every `/*1*/` of the library into
/// `/*2*/`, made once for all the cases.
fn walked() -> &'static Impact {
    static WALKED: std::sync::OnceLock<Impact> = std::sync::OnceLock::new();
    WALKED.get_or_init(|| {
        let new = LIB.replace("/*1*/", "/*2*/");
        let project = Project::new("constructs", &[("Lib.cs", LIB), ("Use.cs", USE)]);
        project.write("Lib.cs", &new);
        let session = project.session();
        let files = parse(&patch("Lib.cs", LIB, &new));
        let limits = Limits {
            depth: 1,
            nodes: 400,
            fan_out: 100,
        };
        walk(&project.root(), &session, &changes(&files[0], &new), limits)
    })
}

/// The members that reach `key` and are not themselves changed, by name.
fn callers_of(impact: &Impact, key: &str) -> Vec<String> {
    let Some(index) = impact.index_of(key) else {
        panic!(
            "{key} is not in the walk: {:?}",
            impact
                .nodes
                .iter()
                .map(|n| n.member.key.as_str())
                .collect::<Vec<_>>()
        );
    };
    let mut found: Vec<String> = impact
        .nodes
        .iter()
        .filter(|n| {
            n.edges.iter().any(|e| {
                e.from == index && matches!(e.relation, Relation::Calls | Relation::CallsBase)
            })
        })
        .filter(|n| n.change.is_none())
        .map(|n| n.member.short_name().to_owned())
        .collect();
    found.sort();
    found
}

/// A conversion operator is a member of its own: a change in its body is a
/// change to it, and its callers are found.
#[test]
fn members_with_no_name_are_changed_and_have_callers() {
    let impact = walked();
    let keys: Vec<&str> = impact
        .nodes
        .iter()
        .filter(|n| n.change.is_some())
        .map(|n| n.member.key.as_str())
        .collect();
    for key in [
        "Money.implicit operator int(Money)",
        "Money.explicit operator Money(int)",
        "Money.+(Money, Money)",
        "Money.true(Money)",
        "Money.this[](int)",
    ] {
        assert!(keys.contains(&key), "{key} among {keys:?}");
    }
}

/// A target-typed `new()` runs the constructor with that many arguments and
/// no other; a `new Money()` and an object initializer run the default one.
#[test]
fn new_without_a_type_calls_the_constructor() {
    let impact = walked();
    assert_eq!(
        callers_of(impact, "Money.Money()"),
        vec!["NewNamed", "NewTarget", "Props"]
    );
    assert_eq!(callers_of(impact, "Money.Money(int)"), vec!["NewInt"]);
}

/// An indexer is run by its brackets; the getter by a read, the setter by an
/// assignment.
#[test]
fn an_indexer_is_called_by_its_brackets() {
    let impact = walked();
    let callers = callers_of(impact, "Money.this[](int)");
    assert!(callers.contains(&"IndexRead".to_owned()), "{callers:?}");
    assert!(callers.contains(&"IndexWrite".to_owned()), "{callers:?}");
    assert!(callers.contains(&"IndexBoth".to_owned()), "{callers:?}");
}

/// Operators, unary and binary, compound assignments and increments.
#[test]
fn operators_are_called_by_their_expressions() {
    let impact = walked();
    assert_eq!(
        callers_of(impact, "Money.+(Money, Money)"),
        vec!["Add", "AddAssign"]
    );
    assert_eq!(callers_of(impact, "Money.-(Money)"), vec!["Neg"]);
    assert_eq!(callers_of(impact, "Money.==(Money, Money)"), vec!["Eq"]);
    assert_eq!(callers_of(impact, "Money.!=(Money, Money)"), vec!["Ne"]);
    assert_eq!(callers_of(impact, "Money.++(Money)"), vec!["Inc"]);
    assert_eq!(callers_of(impact, "Money.true(Money)"), vec!["IfTrue"]);
    assert_eq!(callers_of(impact, "Money.false(Money)"), vec!["AndAlso"]);
    // Another type's operator of the same spelling is another member.
    assert_eq!(
        callers_of(impact, "Other.+(Other, Other)"),
        vec!["AddOther"]
    );
}

/// Implicit and explicit conversions, by where the value changes type.
#[test]
fn conversions_are_called_where_the_type_changes() {
    let impact = walked();
    let callers = callers_of(impact, "Money.implicit operator int(Money)");
    assert_eq!(callers, vec!["Cast", "ToInt"]);
    assert_eq!(
        callers_of(impact, "Money.explicit operator Money(int)"),
        vec!["FromInt"]
    );
    assert_eq!(
        callers_of(impact, "Other.implicit operator int(Other)"),
        vec!["OtherToInt"]
    );
}

/// `ToString` is run where the static type shows the text is written: an
/// interpolation, a concatenation, an argument of `Console.WriteLine`; not
/// where the value is an `object`, and not for another type's `ToString`.
#[test]
fn to_string_is_called_where_the_static_type_shows_it() {
    let impact = walked();
    let mut found = callers_of(impact, "Money.ToString()");
    found.dedup();
    assert!(found.contains(&"Interp".to_owned()), "{found:?}");
    assert!(found.contains(&"Concat".to_owned()), "{found:?}");
    assert!(found.contains(&"Named".to_owned()), "{found:?}");
    assert!(!found.contains(&"AsObject".to_owned()), "{found:?}");
    assert!(!found.contains(&"OtherInterp".to_owned()), "{found:?}");
    assert_eq!(callers_of(impact, "Plain.ToString()"), vec!["WritePlain"]);
    assert_eq!(callers_of(impact, "Other.ToString()"), vec!["OtherInterp"]);
}

/// `using`, `await using` and `foreach` dispose; `foreach` runs the
/// enumerator pattern; a collection initializer calls `Add`.
#[test]
fn using_foreach_and_initializers_call_their_members() {
    let impact = walked();
    assert_eq!(
        callers_of(impact, "Bag.Dispose()"),
        vec!["UsingDecl", "UsingStmt"]
    );
    assert_eq!(
        callers_of(impact, "Later.DisposeAsync()"),
        vec!["AwaitUsing"]
    );
    assert_eq!(callers_of(impact, "Bag.GetEnumerator()"), vec!["Each"]);
    assert_eq!(callers_of(impact, "Bag.Walker.MoveNext()"), vec!["Each"]);
    assert_eq!(callers_of(impact, "Bag.Walker.Current"), vec!["Each"]);
    assert_eq!(callers_of(impact, "Bag.Walker.Dispose()"), vec!["Each"]);
    assert_eq!(callers_of(impact, "Bag.Add(int)"), vec!["Init"]);
}

/// Deconstruction, `await`, list patterns, queries, `with` and attributes.
#[test]
fn patterns_await_queries_with_and_attributes_call_their_members() {
    let impact = walked();
    assert_eq!(
        callers_of(impact, "Money.Deconstruct(int, int)"),
        vec!["Decon", "PatternDecon"]
    );
    assert_eq!(callers_of(impact, "Wait.GetAwaiter()"), vec!["Await"]);
    assert_eq!(
        callers_of(impact, "Wait.Awaiter.GetResult()"),
        vec!["Await"]
    );
    assert_eq!(
        callers_of(impact, "Wait.Awaiter.IsCompleted"),
        vec!["Await"]
    );
    assert_eq!(callers_of(impact, "Items.Length"), vec!["ListPattern"]);
    assert_eq!(
        callers_of(impact, "Q.Select(Func<int, int>)"),
        vec!["Query"]
    );
    assert_eq!(
        callers_of(impact, "Q.Where(Func<int, bool>)"),
        vec!["Query"]
    );
    assert_eq!(callers_of(impact, "Rec.Rec(Rec)"), vec!["With"]);
    assert_eq!(
        callers_of(impact, "MyAttribute.MyAttribute(int)"),
        vec!["Marked"]
    );
}

/// A method group made a delegate and a handler of an event are uses; the
/// name in `nameof`, in `typeof` and in a `cref` is not.
#[test]
fn a_method_group_is_a_call_and_nameof_typeof_and_cref_are_not() {
    let impact = walked();
    assert_eq!(callers_of(impact, "Money.Compute()"), vec!["Group"]);
    assert_eq!(callers_of(impact, "Events.Handler()"), vec!["Subscribe"]);
}

/// The getter and the setter of a property are different code: whoever only
/// assigns it does not run a changed getter, and whoever only reads it does
/// not run a changed setter.
#[test]
fn a_getter_and_a_setter_have_their_own_callers() {
    let old = "class P {\n    int v;\n    public int X {\n        get { return v; }\n        set { v = value; }\n    }\n}\n";
    let user = "class U {\n    void Read(P p) { int a = p.X; }\n    void Write(P p) { p.X = 1; }\n    void Both(P p) { p.X += 1; }\n}\n";
    let walk_of = |new: &str| {
        let project = Project::new("accessors", &[("P.cs", old), ("U.cs", user)]);
        project.write("P.cs", new);
        let session = project.session();
        let files = parse(&patch("P.cs", old, new));
        let found = changes(&files[0], new);
        let touched = found[0].touched;
        let impact = walk(&project.root(), &session, &found, Limits::default());
        (impact, touched)
    };
    let (impact, touched) = walk_of(&old.replace("return v;", "return v + 1;"));
    assert_eq!(touched, Touched::Getter);
    assert_eq!(callers_of(&impact, "P.X"), vec!["Both", "Read"]);
    let (impact, touched) = walk_of(&old.replace("v = value;", "v = value + 1;"));
    assert_eq!(touched, Touched::Setter);
    assert_eq!(callers_of(&impact, "P.X"), vec!["Both", "Write"]);
}

/// Two members written on one line are told apart: the one that changed is
/// the one the change is attributed to, not the class.
#[test]
fn members_on_one_line_are_told_apart() {
    let old = "class A { void F() { int a = 1; } void G() { int b = 1; } }\n";
    let new = old.replace("int b = 1;", "int b = 2;");
    let files = parse(&patch("A.cs", old, &new));
    let found: Vec<String> = changes(&files[0], &new)
        .into_iter()
        .map(|c| c.member.key)
        .collect();
    assert_eq!(found, vec!["A.G()".to_owned()]);
}

/// A change in code the build leaves out is not lost: it is the member's,
/// named, and said to be in code that is not built.
#[test]
fn a_change_in_an_inactive_region_is_named_and_marked() {
    let old = "class A {\n#if NOPE\n    void F() { int x = 1; }\n#endif\n    void G() { int y = 1; }\n}\n";
    let new = old.replace("int x = 1;", "int x = 2;");
    let files = parse(&patch("A.cs", old, &new));
    let found = changes(&files[0], &new);
    let seen: Vec<(&str, bool)> = found
        .iter()
        .map(|c| (c.member.key.as_str(), c.inactive))
        .collect();
    assert_eq!(seen, vec![("A.F()", true)]);
    // A change in the part that is built is as it was.
    let new = old.replace("int y = 1;", "int y = 2;");
    let files = parse(&patch("A.cs", old, &new));
    let seen: Vec<(String, bool)> = changes(&files[0], &new)
        .into_iter()
        .map(|c| (c.member.key, c.inactive))
        .collect();
    assert_eq!(seen, vec![("A.G()".to_owned(), false)]);
}

/// A caller written on a line with other members is the member the compiler
/// names, not the class that holds them all.
#[test]
fn a_caller_on_a_line_with_other_members_is_that_member() {
    let old = "class A { public void F() { int a = 1; } }\nclass B { void G() { new A().F(); } void H() { } }\n";
    let new = old.replace("int a = 1;", "int a = 2;");
    let project = Project::new("one-line", &[("A.cs", old)]);
    project.write("A.cs", &new);
    let session = project.session();
    let files = parse(&patch("A.cs", old, &new));
    let impact = walk(
        &project.root(),
        &session,
        &changes(&files[0], &new),
        Limits::default(),
    );
    let keys: Vec<&str> = impact.nodes.iter().map(|n| n.member.key.as_str()).collect();
    assert_eq!(keys, vec!["A.F()", "B.G()"]);
}

/// A source that is not UTF-8 is read as Latin-1, as the compiler reads it:
/// its members are found, changed and called, and not dropped.
#[test]
fn a_latin_1_source_is_read_as_the_compiler_reads_it() {
    use super::Extensions;
    use super::report::{Request, analyze};

    let new = b"class C {\n    // caf\xe9\n    public int F() { return 2; }\n}\n";
    let user = "class U {\n    int G(C c) { return c.F(); }\n}\n";
    let project = Project::new("latin", &[("U.cs", user)]);
    project.write_bytes("C.cs", new);
    let session = project.session();
    // What `git diff` prints: the bytes of the file, decoded by line.
    let patch = rustlyn_ide::document::decode_lines(
        b"--- a/C.cs\n+++ b/C.cs\n@@ -1,4 +1,4 @@\n class C {\n     // caf\xe9\n-    public int F() { return 1; }\n+    public int F() { return 2; }\n }\n",
    );
    let report = analyze(
        &Request::new(project.root(), patch),
        &session,
        &Extensions::default(),
    );
    let keys: Vec<&str> = report
        .impact
        .nodes
        .iter()
        .map(|n| n.member.key.as_str())
        .collect();
    assert_eq!(keys, vec!["C.F()", "U.G(C)"]);
}

/// `Relation` of a call through a construct is a call, like any other.
#[test]
fn a_construct_is_a_plain_call() {
    let impact = walked();
    let index = impact.index_of("Money.+(Money, Money)").expect("changed");
    let caller = impact.index_of("Use.Add(Money, Money)").expect("reached");
    let edge = impact.nodes[caller]
        .edges
        .iter()
        .find(|e| e.from == index)
        .expect("an edge");
    assert_eq!(edge.relation, Relation::Calls);
}

/// The walk of a change to one file of a project: `old` is what the file
/// was, `new` what it is on disk.
fn walked_change(files: &[(&str, &str)], path: &str, old: &str, new: &str, depth: usize) -> Impact {
    let mut all: Vec<(&str, &str)> = files.to_vec();
    all.push((path, new));
    let project = Project::new("changed", &all);
    let session = project.session();
    let parsed = parse(&patch(path, old, new));
    let limits = Limits {
        depth,
        nodes: 400,
        fan_out: 100,
    };
    walk(&project.root(), &session, &changes(&parsed[0], new), limits)
}

/// The members reached from `key` by reading what it writes, by name.
fn readers_of(impact: &Impact, key: &str) -> Vec<String> {
    let index = impact.index_of(key).expect("in the walk");
    let mut found: Vec<String> = impact
        .nodes
        .iter()
        .filter(|n| {
            n.edges
                .iter()
                .any(|e| e.from == index && e.relation == Relation::Reads)
        })
        .map(|n| n.member.short_name().to_owned())
        .collect();
    found.sort();
    found
}

const GENERIC: &str = "class Base {
  public static implicit operator int(Base b) { return 1; }
  public static bool operator ==(Base a, Base b) { return true; }
  public static bool operator !=(Base a, Base b) { return false; }
  public override bool Equals(object o) { return true; }
  public override int GetHashCode() { return 1; }
  public int this[int i] { get { return i; } }
}
class Gen<T> where T : Base {
  public int Conv(T a) { int i = a; return i; }
  public bool Eq(T a, T b) { return a == b; }
  public int Idx(T a) { return a[0]; }
}
class Loose<T> {
  public bool Eq(T a, T b) { return false; }
}
";

/// A value of a type parameter runs the members of its constraint, and the
/// body that does so never writes the constraint's name.
#[test]
fn a_change_reaches_the_bodies_that_use_it_through_a_constraint() {
    let new = GENERIC.replace(
        "return 1; }\n  public static bool",
        "return 2; }\n  public static bool",
    );
    let impact = walked_change(&[], "A.cs", GENERIC, &new, 1);
    assert_eq!(
        callers_of(&impact, "Base.implicit operator int(Base)"),
        vec!["Conv"]
    );
    let new = GENERIC.replace(
        "operator ==(Base a, Base b) { return true; }",
        "operator ==(Base a, Base b) { return false; }",
    );
    let impact = walked_change(&[], "A.cs", GENERIC, &new, 1);
    assert_eq!(callers_of(&impact, "Base.==(Base, Base)"), vec!["Eq"]);
    let new = GENERIC.replace("get { return i; }", "get { return i + 1; }");
    let impact = walked_change(&[], "A.cs", GENERIC, &new, 1);
    assert_eq!(callers_of(&impact, "Base.this[](int)"), vec!["Idx"]);
}

const CONDITIONAL: &str = "class Coll {
  public override string ToString() { return \"C\"; }
  public override bool Equals(object o) { return false; }
  public override int GetHashCode() { return 1; }
}
class Use {
  void f1(Coll a) { var s = a.ToString(); }
  void f2(Coll a) { var s = a?.ToString(); }
  void f4(Coll a) { var s = a?.Equals(null); }
  void f5(Coll a) { var s = a?.GetHashCode(); }
  void f9(Coll a) { var s = object.Equals(a, a); }
  void g2(object o) { var s = o?.ToString(); }
}
";

/// `a?.ToString()` runs the override of the type of `a`.
#[test]
fn a_conditional_call_of_an_override_is_a_call() {
    let new = CONDITIONAL.replace("return \"C\";", "return \"D\";");
    let impact = walked_change(&[], "A.cs", CONDITIONAL, &new, 1);
    assert_eq!(callers_of(&impact, "Coll.ToString()"), vec!["f1", "f2"]);
    let new = CONDITIONAL.replace("return false;", "return true;");
    let impact = walked_change(&[], "A.cs", CONDITIONAL, &new, 1);
    assert_eq!(callers_of(&impact, "Coll.Equals(object)"), vec!["f4"]);
    let new = CONDITIONAL.replace("GetHashCode() { return 1; }", "GetHashCode() { return 2; }");
    let impact = walked_change(&[], "A.cs", CONDITIONAL, &new, 1);
    assert_eq!(callers_of(&impact, "Coll.GetHashCode()"), vec!["f5"]);
}

const ACCESSORS: &str = "class P {
  int _v;
  public int Prop {
    get {
      return _v;
    }
    set {
      _v = value;
    }
  }
  public int this[int i] {
    get {
      return i;
    }
    set {
      _v = i;
    }
  }
}
class U {
  int r1(P p) => p.Prop;
  void w1(P p) { p.Prop = 1; }
  void rw1(P p) { p.Prop += 1; }
  int ri(P p) => p[0];
  void wi(P p) { p[0] = 1; }
}
";

/// A field read in a getter makes the callers of the getter affected, not
/// those that only run the setter.
#[test]
fn a_property_that_reads_a_field_in_its_getter_is_read_by_the_getters_callers() {
    // The indexer's setter writes `_v`; the getter of `Prop` reads it.
    let new = ACCESSORS.replace("_v = i;", "_v = i + 1;");
    let impact = walked_change(&[], "A.cs", ACCESSORS, &new, 4);
    assert_eq!(readers_of(&impact, "P._v"), vec!["Prop"]);
    assert_eq!(callers_of(&impact, "P.Prop"), vec!["r1", "rw1"]);
    // The setter of `Prop` writes it, and nothing of the property reads it.
    let new = ACCESSORS.replace("_v = value;", "_v = value + 1;");
    let impact = walked_change(&[], "A.cs", ACCESSORS, &new, 4);
    assert_eq!(callers_of(&impact, "P.Prop"), vec!["rw1", "w1"]);
    // A change to the getter itself: those that read it.
    let new = ACCESSORS.replace("return _v;", "return _v + 1;");
    let impact = walked_change(&[], "A.cs", ACCESSORS, &new, 1);
    assert_eq!(callers_of(&impact, "P.Prop"), vec!["r1", "rw1"]);
}

/// A property that reads a field in both accessors is run by every caller.
#[test]
fn a_property_that_reads_in_both_accessors_has_every_caller() {
    let old = ACCESSORS.replace("_v = value;", "_v = value + _v;");
    let new = old.replace("_v = i;", "_v = i + 1;");
    let impact = walked_change(&[], "A.cs", &old, &new, 4);
    assert_eq!(callers_of(&impact, "P.Prop"), vec!["r1", "rw1", "w1"]);
}

const NAMES: &str = "class A {
  public int X;
  public void Set() { X = 1; }
}
class U {
  int r8(A a) { return nameof(a.X).Length; }
  const string K = nameof(A.X);
  int r(A a) { return a.X; }
  string s(A a) { return nameof ( a.X ); }
}
";

/// `nameof` names a field and reads nothing.
#[test]
fn nameof_is_not_a_read() {
    let new = NAMES.replace("X = 1;", "X = 2;");
    let impact = walked_change(&[], "A.cs", NAMES, &new, 2);
    assert_eq!(readers_of(&impact, "A.X"), vec!["r"]);
}

const TWINS: &str = "interface IShape { double Area(); }
class Square : IShape {
  double IShape.Area() => 3;
  public double Area() => 4;
}
class Use {
  void u4(Square s) { s.Area(); }
  void u5(IShape s) { s.Area(); }
}
";

/// Members of a type with one name are two members, whichever is written
/// first: the change is to the one whose lines it is on.
#[test]
fn an_explicit_implementation_and_a_public_member_of_one_name_are_apart() {
    let new = TWINS.replace("=> 4;", "=> 44;");
    let impact = walked_change(&[], "A.cs", TWINS, &new, 1);
    let changed: Vec<(&str, Option<How>)> = impact
        .nodes
        .iter()
        .filter(|n| n.change.is_some())
        .map(|n| (n.member.key.as_str(), n.change))
        .collect();
    assert_eq!(changed, vec![("Square.Area()", Some(How::Body))]);
    assert_eq!(callers_of(&impact, "Square.Area()"), vec!["u4"]);
    let new = TWINS.replace("=> 3;", "=> 33;");
    let impact = walked_change(&[], "A.cs", TWINS, &new, 1);
    assert_eq!(callers_of(&impact, "Square.IShape.Area()"), vec!["u5"]);
    assert!(impact.index_of("Square.Area()").is_none());
}

const ONE_LINE: &str = "class C { public int A() { return 1; } public int B() { return 2; } public int P { get; set; } }\n";

fn changed_keys(old: &str, new: &str) -> Vec<(String, How)> {
    let files = parse(&patch("A.cs", old, new));
    changes(&files[0], new)
        .into_iter()
        .map(|change| (change.member.key, change.how))
        .collect()
}

/// A change on a line that holds several members is to the member the bytes
/// are in; where the bytes cannot say, to each of the members on the line,
/// and not to the type around them.
#[test]
fn a_change_on_a_line_of_several_members_is_to_the_member_it_is_in() {
    let new = ONE_LINE.replace("{ get; set; } }", "{ get; set; } = 3; }");
    assert_eq!(
        changed_keys(ONE_LINE, &new),
        vec![("C.P".to_owned(), How::Body)]
    );
    let new = ONE_LINE.replace("return 2;", "return 3;");
    assert_eq!(
        changed_keys(ONE_LINE, &new),
        vec![("C.B()".to_owned(), How::Body)]
    );
    let new = ONE_LINE.replace("return 1;", "return 4;");
    assert_eq!(
        changed_keys(ONE_LINE, &new),
        vec![("C.A()".to_owned(), How::Body)]
    );
    // A comment after the members is to each of them, not to the type.
    let new = ONE_LINE.replace(" }\n", " } // x\n");
    let keys: Vec<String> = changed_keys(ONE_LINE, &new)
        .into_iter()
        .map(|(k, _)| k)
        .collect();
    assert!(!keys.contains(&"C".to_owned()), "{keys:?}");
}

/// A property with an initializer on one line is the same member as on
/// several: its callers are reached.
#[test]
fn an_initializer_added_on_a_line_of_members_reaches_the_properties_callers() {
    let user = "class U { int up(C c) { return c.P; } int ua(C c) { return c.A(); } }\n";
    let new = ONE_LINE.replace("{ get; set; } }", "{ get; set; } = 3; }");
    let impact = walked_change(&[("U.cs", user)], "A.cs", ONE_LINE, &new, 1);
    assert_eq!(callers_of(&impact, "C.P"), vec!["up"]);
    assert!(impact.index_of("C.A()").is_none());
}

const FORWARDING: &str = "using System.Collections;
interface IShape { double Area(); }
class Sq : IShape, IEnumerable {
  public double Area() => 4;
  double IShape.Area() => Area();
  public IEnumerator GetEnumerator() => null;
  IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}
class Use {
  void a(IShape s) { s.Area(); }
  void b(IEnumerable e) { e.GetEnumerator(); }
}
";

/// An explicit implementation that forwards to the member that changed is a
/// caller of it, and what calls it through its interface may run it.
#[test]
fn a_forwarding_explicit_implementation_is_a_caller_and_is_called_through_its_interface() {
    let new = FORWARDING.replace("Area() => 4;", "Area() => 44;");
    let impact = walked_change(&[], "A.cs", FORWARDING, &new, 3);
    assert_eq!(callers_of(&impact, "Sq.Area()"), vec!["Area"]);
    assert_eq!(callers_of(&impact, "Sq.IShape.Area()"), vec!["a"]);
    let new = FORWARDING.replace("GetEnumerator() => null;", "GetEnumerator() => null; // x");
    let impact = walked_change(&[], "A.cs", FORWARDING, &new, 3);
    assert_eq!(
        callers_of(&impact, "Sq.GetEnumerator()"),
        vec!["GetEnumerator"]
    );
    assert_eq!(
        callers_of(&impact, "Sq.IEnumerable.GetEnumerator()"),
        vec!["b"]
    );
}
