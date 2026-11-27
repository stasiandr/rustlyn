//! Who reaches a member without writing its name, by construction: each
//! caller below is a member of its own, and what it does is what C# runs.

use std::path::Path;

use super::super::UseKind;
use super::super::tests::{at, compile};
use super::*;

const LIB: &str = r#"using System;
using System.Collections;
using System.Collections.Generic;
using System.Threading.Tasks;

public class Money
{
    public int V;
    public Money() { }
    public Money(int v) { V = v; }
    public int this[int i] { get { return V + i; } set { V = value; } }
    public static Money operator +(Money a, Money b) { return a; }
    public static Money operator -(Money a) { return a; }
    public static Money operator &(Money a, Money b) { return a; }
    public static bool operator ==(Money a, Money b) { return true; }
    public static bool operator !=(Money a, Money b) { return false; }
    public static Money operator ++(Money a) { return a; }
    public static bool operator true(Money a) { return true; }
    public static bool operator false(Money a) { return false; }
    public static implicit operator int(Money m) { return m.V; }
    public static explicit operator Money(int v) { return new Money(v); }
    public override bool Equals(object o) { return true; }
    public override int GetHashCode() { return 1; }
    public override string ToString() { return "m"; }
    public int P { get { return V; } set { V = value; } }
    public int Compute() { return V; }
    public void Deconstruct(out int a, out int b) { a = 1; b = 2; }
}

public class Plain
{
    public override string ToString() { return "p"; }
}

public class Other
{
    public static Other operator +(Other a, Other b) { return a; }
    public static implicit operator int(Other o) { return 0; }
    public override string ToString() { return "o"; }
    public int Compute() { return 0; }
}

public class Bag : IDisposable
{
    public void Dispose() { }
    public void Add(int v) { }
    public Bag.Walker GetEnumerator() { return new Walker(); }
    public class Walker : IDisposable
    {
        public bool MoveNext() { return false; }
        public int Current { get { return 0; } }
        public void Dispose() { }
    }
}

public class Later : IAsyncDisposable
{
    public ValueTask DisposeAsync() { return default; }
}

public class Wait
{
    public Wait.Awaiter GetAwaiter() { return new Awaiter(); }
    public class Awaiter : System.Runtime.CompilerServices.INotifyCompletion
    {
        public bool IsCompleted { get { return true; } }
        public int GetResult() { return 1; }
        public void OnCompleted(Action continuation) { }
    }
}

public class Q
{
    public Q Select(Func<int, int> f) { return this; }
    public Q Where(Func<int, bool> f) { return this; }
}

public class Items
{
    public int Length { get { return 2; } }
    public int this[int i] { get { return i; } }
}

public record Rec
{
    public int X { get; init; }
    public Rec() { }
    protected Rec(Rec original) { X = original.X; }
}

public class MyAttribute : Attribute
{
    public MyAttribute(int v) { }
    public MyAttribute(string s) { }
    public string Name { get; set; }
}

public class Seq : IEnumerable<int>, IDisposable
{
    public void Dispose() { }
    public IEnumerator<int> GetEnumerator() { yield return 1; }
    IEnumerator IEnumerable.GetEnumerator() { return GetEnumerator(); }
}

public class Events
{
    public event Action Fired;
    public void Handler() { }
    public int Number() { return 1; }
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
    public Money AddOther(Other a, Other b) { return a + b == null ? null : null; }
    public Money Neg(Money a) { return -a; }
    public bool Eq(Money a, Money b) { return a == b; }
    public bool Ne(Money a, Money b) { return a != b; }
    public Money Inc(Money a) { a++; return a; }
    public Money PreInc(Money a) { return ++a; }
    public int IfTrue(Money a) { if (a) { return 1; } return 0; }
    public Money AndAlso(Money a, Money b) { return a && b; }
    public int ToInt(Money m) { int i = m; return i; }
    public int Cast(Money m) { return (int)m; }
    public int ArgInt(Money m) { return Take(m); }
    public int Take(int i) { return i; }
    public int OtherToInt(Other o) { int i = o; return i; }
    public Money FromInt(int i) { return (Money)i; }
    public string Interp(Money m) { return $"{m}"; }
    public string Concat(Money m) { return "a" + m; }
    public string Named(Money m) { return m.ToString(); }
    public string AsObject(Money m) { object o = m; return $"{o}"; }
    public string OtherInterp(Other o) { return $"{o}"; }
    public void Write(Money m) { Console.WriteLine(m); }
    public void WritePlain(Plain p) { Console.WriteLine(p); }
    public string FormatPlain(Plain p) { return string.Format("{0}", p); }
    public void UsingStmt(Bag b) { using (b) { } }
    public void UsingDecl() { using var b = new Bag(); }
    public void Direct(Bag b) { b.Dispose(); }
    public async Task AwaitUsing(Later l) { await using (l) { } }
    public void Each(Bag b) { foreach (var x in b) { } }
    public Bag Init() { return new Bag { 1, 2 }; }
    public Money Props() { return new Money { P = 4 }; }
    public void SetP(Money m) { m.P = 4; }
    public int GetP(Money m) { return m.P; }
    public void BothP(Money m) { m.P += 1; }
    public int Decon(Money m) { var (a, b) = m; return a + b; }
    public int Decon2(Money m) { int x; int y; (x, y) = m; return x + y; }
    public bool PatternDecon(Money m) { return m is (1, _); }
    public async Task<int> Await(Wait w) { return await w; }
    public bool ListPattern(Items i) { return i is [1, ..]; }
    public Q Query(Q q) { return from x in q where x > 1 select x + 1; }
    public Rec With(Rec r) { return r with { X = 2 }; }
    public Rec WithNothing(Rec r) { return r with { }; }
    [My(3)] public int Marked;
    [My("s", Name = "x")] public int MarkedString;
    public Func<int> Group(Money m) { Func<int> f = m.Compute; return f; }
    public int Nameof() { return nameof(Money.Compute).Length; }
    public Type Typeof() { return typeof(Money); }
    /// <see cref="Money.Compute"/>
    public int Doc() { return 0; }
    public void Subscribe(Events e) { e.Fired += e.Handler; }
    public void EachSeq(Seq s) { foreach (var x in s) { } }
    public void ViaInterface(Seq s) { IDisposable d = s; using (d) { } }
}
"#;

fn project() -> Option<Semantic> {
    compile(&[("Lib.cs", LIB), ("Use.cs", USE)], true)
}

/// The members that reach what is declared at `marker` in `Lib.cs`, with how.
fn reached(semantic: &Semantic, marker: &str, into: usize) -> Vec<(String, UseKind)> {
    let path = Path::new("/p/Lib.cs");
    let symbol = semantic
        .call_hierarchy_item(path, at(LIB, marker, into), None)
        .unwrap_or_else(|| panic!("a member at {marker}"))
        .symbol;
    let mut found: Vec<(String, UseKind)> = semantic
        .incoming_calls(symbol)
        .iter()
        .filter(|call| !call.through_base)
        .flat_map(|call| {
            call.uses
                .iter()
                .map(|&kind| (call.from.name.clone(), kind))
                .collect::<Vec<_>>()
        })
        .collect();
    found.sort();
    found.dedup();
    found
}

fn names(found: &[(String, UseKind)]) -> Vec<&str> {
    found.iter().map(|(name, _)| name.as_str()).collect()
}

/// A target-typed `new()` runs the constructor with that many arguments and
/// no other.
#[test]
fn a_target_typed_new_calls_the_constructor_it_binds() {
    let Some(semantic) = project() else { return };
    assert_eq!(
        names(&reached(&semantic, "Money() { }", 0)),
        vec!["NewNamed", "NewTarget", "Props"]
    );
    assert_eq!(
        names(&reached(&semantic, "Money(int v)", 0)),
        vec!["NewInt", "op_Explicit"]
    );
}

/// An indexer's getter and setter are different code: `m[3]` reads,
/// `m[3] = 1` writes and `m[3] += 1` does both.
#[test]
fn an_indexer_is_called_by_its_brackets_with_the_accessor_it_runs() {
    let Some(semantic) = project() else { return };
    assert_eq!(
        reached(&semantic, "this[int i]", 0),
        vec![
            ("IndexBoth".to_string(), UseKind::ReadWrite),
            ("IndexRead".to_string(), UseKind::Read),
            ("IndexWrite".to_string(), UseKind::Write),
        ]
    );
}

/// An operator is called by the expression that uses it, a compound
/// assignment included, and by no other type's operator of the same symbol.
#[test]
fn operators_are_called_by_their_expressions() {
    let Some(semantic) = project() else { return };
    assert_eq!(
        names(&reached(&semantic, "+(Money a, Money b)", 0)),
        vec!["Add", "AddAssign"]
    );
    assert_eq!(names(&reached(&semantic, "-(Money a)", 0)), vec!["Neg"]);
    assert_eq!(names(&reached(&semantic, "==(Money a", 0)), vec!["Eq"]);
    assert_eq!(names(&reached(&semantic, "!=(Money a", 0)), vec!["Ne"]);
    assert_eq!(
        names(&reached(&semantic, "++(Money a)", 0)),
        vec!["Inc", "PreInc"]
    );
    assert_eq!(
        names(&reached(&semantic, "true(Money a)", 0)),
        vec!["IfTrue"]
    );
    assert_eq!(
        names(&reached(&semantic, "false(Money a)", 0)),
        vec!["AndAlso"]
    );
    assert_eq!(names(&reached(&semantic, "&(Money a", 0)), vec!["AndAlso"]);
}

/// A conversion runs wherever a value of the one type is taken as the
/// other: assigned, passed, cast.
#[test]
fn conversions_are_called_where_the_value_changes_type() {
    let Some(semantic) = project() else { return };
    assert_eq!(
        names(&reached(&semantic, "operator int(Money", 0)),
        vec!["ArgInt", "Cast", "ToInt", "Write"]
    );
    assert_eq!(
        names(&reached(&semantic, "operator Money(int", 0)),
        vec!["FromInt"]
    );
}

/// `ToString` runs where the static type shows it is written as text: an
/// interpolation hole, a string concatenation, an argument of
/// `Console.WriteLine`. A value typed `object` shows nothing.
#[test]
fn to_string_is_called_where_the_static_type_shows_it() {
    let Some(semantic) = project() else { return };
    let found = reached(&semantic, "ToString() { return \"m\"", 0);
    assert_eq!(names(&found), vec!["Concat", "Interp", "Named"]);
    let plain = reached(&semantic, "ToString() { return \"p\"", 0);
    assert_eq!(names(&plain), vec!["FormatPlain", "WritePlain"]);
    let other = reached(&semantic, "ToString() { return \"o\"", 0);
    assert_eq!(names(&other), vec!["OtherInterp"]);
}

/// `using` and `foreach` dispose; the call the code writes is a caller as
/// before.
#[test]
fn using_and_foreach_call_dispose() {
    let Some(semantic) = project() else { return };
    assert_eq!(
        names(&reached(&semantic, "Dispose() { }\n    public void Add", 0)),
        vec!["Direct", "UsingDecl", "UsingStmt"]
    );
    assert_eq!(
        names(&reached(&semantic, "DisposeAsync()", 0)),
        vec!["AwaitUsing"]
    );
    assert_eq!(
        names(&reached(&semantic, "Dispose() { }\n    }", 0)),
        vec!["Each"]
    );
}

/// `foreach` runs the pattern's `GetEnumerator`, `MoveNext` and `Current`.
#[test]
fn foreach_calls_the_enumerator_pattern() {
    let Some(semantic) = project() else { return };
    assert_eq!(
        names(&reached(&semantic, "GetEnumerator()", 0)),
        vec!["Each"]
    );
    assert_eq!(names(&reached(&semantic, "MoveNext()", 0)), vec!["Each"]);
    assert_eq!(names(&reached(&semantic, "Current {", 0)), vec!["Each"]);
}

/// A collection initializer calls `Add` for each element.
#[test]
fn a_collection_initializer_calls_add() {
    let Some(semantic) = project() else { return };
    assert_eq!(names(&reached(&semantic, "Add(int v)", 0)), vec!["Init"]);
}

/// An object initializer assigns, and `m.P = 4` assigns: setters, not
/// getters.
#[test]
fn a_property_setter_is_reached_by_assignment_and_initializers() {
    let Some(semantic) = project() else { return };
    assert_eq!(
        reached(&semantic, "P {", 0),
        vec![
            ("BothP".to_string(), UseKind::ReadWrite),
            ("GetP".to_string(), UseKind::Read),
            ("Props".to_string(), UseKind::Write),
            ("SetP".to_string(), UseKind::Write),
        ]
    );
}

/// A deconstruction, in a declaration, an assignment or a positional
/// pattern, calls `Deconstruct`.
#[test]
fn deconstruction_calls_deconstruct() {
    let Some(semantic) = project() else { return };
    assert_eq!(
        names(&reached(&semantic, "Deconstruct(out", 0)),
        vec!["Decon", "Decon2", "PatternDecon"]
    );
}

/// `await x` runs `GetAwaiter`, `IsCompleted` and `GetResult`.
#[test]
fn await_calls_the_awaiter_pattern() {
    let Some(semantic) = project() else { return };
    assert_eq!(names(&reached(&semantic, "GetAwaiter()", 0)), vec!["Await"]);
    assert_eq!(names(&reached(&semantic, "GetResult()", 0)), vec!["Await"]);
    assert_eq!(
        names(&reached(&semantic, "IsCompleted {", 0)),
        vec!["Await"]
    );
}

/// A list pattern reads `Length` and the indexer.
#[test]
fn a_list_pattern_reads_length_and_the_indexer() {
    let Some(semantic) = project() else { return };
    assert_eq!(
        names(&reached(&semantic, "Length {", 0)),
        vec!["ListPattern"]
    );
    assert_eq!(
        names(&reached(&semantic, "this[int i] { get { return i", 0)),
        vec!["ListPattern"]
    );
}

/// A query expression calls the query methods it is written with.
#[test]
fn a_query_calls_select_and_where() {
    let Some(semantic) = project() else { return };
    assert_eq!(names(&reached(&semantic, "Select(Func", 0)), vec!["Query"]);
    assert_eq!(names(&reached(&semantic, "Where(Func", 0)), vec!["Query"]);
}

/// `with` runs the record's own copy constructor and the setters it names.
#[test]
fn with_calls_the_copy_constructor_and_the_init_setters() {
    let Some(semantic) = project() else { return };
    assert_eq!(
        names(&reached(&semantic, "Rec(Rec original)", 0)),
        vec!["With", "WithNothing"]
    );
    // The copy constructor assigns it too, as a member of its own.
    assert_eq!(
        reached(&semantic, "X {", 0),
        vec![
            ("Rec".to_string(), UseKind::Read),
            ("Rec".to_string(), UseKind::Write),
            ("With".to_string(), UseKind::Write),
        ]
    );
}

/// An attribute calls the constructor it binds and sets its named
/// properties; the member it is on is the caller.
#[test]
fn an_attribute_calls_its_constructor() {
    let Some(semantic) = project() else { return };
    assert_eq!(
        names(&reached(&semantic, "MyAttribute(int v)", 0)),
        vec!["Marked"]
    );
    assert_eq!(
        names(&reached(&semantic, "MyAttribute(string s)", 0)),
        vec!["MarkedString"]
    );
    assert_eq!(
        reached(&semantic, "Name {", 0),
        vec![("MarkedString".to_string(), UseKind::Write)]
    );
}

/// A method group made a delegate, and a handler subscribed to an event, are
/// uses of the method; `nameof`, `typeof` and a `cref` are not.
#[test]
fn a_method_group_is_a_call_and_a_name_in_nameof_is_not() {
    let Some(semantic) = project() else { return };
    assert_eq!(
        names(&reached(&semantic, "Compute() { return V", 0)),
        vec!["Group"]
    );
    assert_eq!(
        names(&reached(&semantic, "Handler()", 0)),
        vec!["Subscribe"]
    );
}

/// Find all references of an indexer lists the `x[i]` that run it, read or
/// written, though no name is there to search for.
#[test]
fn find_references_of_an_indexer_lists_its_brackets() {
    let Some(semantic) = project() else { return };
    let path = Path::new("/p/Lib.cs");
    let (_, found) = semantic
        .references_detailed(path, at(LIB, "this[int i]", 0), None)
        .expect("references");
    let mut uses: Vec<(String, super::super::ReferenceKind)> = found
        .iter()
        .filter(|found| found.path.ends_with("Use.cs"))
        .map(|found| (found.container.clone(), found.kind))
        .collect();
    uses.sort_by(|a, b| a.0.cmp(&b.0));
    assert_eq!(
        uses,
        vec![
            (
                "Use.IndexBoth".to_string(),
                super::super::ReferenceKind::Write
            ),
            (
                "Use.IndexRead".to_string(),
                super::super::ReferenceKind::Read
            ),
            (
                "Use.IndexWrite".to_string(),
                super::super::ReferenceKind::Write
            ),
        ]
    );
}

/// The names of a file with the uses that write none: what a project-wide
/// graph is made of.
#[test]
fn links_carry_the_uses_no_name_stands_for() {
    let Some(semantic) = project() else { return };
    let links = semantic.links(Path::new("/p/Use.cs")).expect("links");
    let hit = |marker: &str, kind: UseKind| {
        let line = USE[..at(USE, marker, 0) as usize].matches('\n').count() as u32;
        links
            .links
            .iter()
            .filter(|link| link.line == line && link.implicit == Some(kind))
            .map(|link| semantic.link_target(link.target).name)
            .collect::<Vec<_>>()
    };
    assert_eq!(hit("Money m = new();", UseKind::Call), vec![".ctor"]);
    assert_eq!(hit("return m[3];", UseKind::Read), vec!["this[]"]);
    assert_eq!(hit("m[3] = 1;", UseKind::Write), vec!["this[]"]);
    assert_eq!(hit("return a + b; }", UseKind::Call), vec!["op_Addition"]);
    assert_eq!(hit("using (b)", UseKind::Call), vec!["Dispose"]);
    assert_eq!(hit("m.P = 4;", UseKind::Write).len(), 0, "a name is a name");
}

/// `foreach` disposes the enumerator it is given, not the collection: the
/// `Dispose` of a type that is both is not run by `foreach` over it. A
/// `using` of the same value as an interface is every implementation's, and
/// is not listed.
#[test]
fn a_use_of_a_base_member_on_another_type_is_not_a_use_of_the_member() {
    let Some(semantic) = project() else { return };
    let path = Path::new("/p/Lib.cs");
    let symbol = semantic
        .call_hierarchy_item(
            path,
            at(LIB, "Dispose() { }\n    public IEnumerator<int>", 0),
            None,
        )
        .expect("Seq.Dispose")
        .symbol;
    let calls = semantic.incoming_calls(symbol);
    let from: Vec<(String, bool)> = calls
        .iter()
        .map(|call| (call.from.name.clone(), call.through_base))
        .collect();
    assert_eq!(from, Vec::<(String, bool)>::new());
}

const CONSTRAINED: &str = r#"public interface IShape { int Size(); int this[int i] { get; } }
public class Base
{
    public static Base operator +(Base a, Base b) { return a; }
    public static implicit operator int(Base b) { return 1; }
    public static bool operator ==(Base a, Base b) { return true; }
    public static bool operator !=(Base a, Base b) { return false; }
    public override bool Equals(object o) { return true; }
    public override int GetHashCode() { return 1; }
    public int this[int i] { get { return i; } }
}
public class Child : Base { }
public class Alien { public static implicit operator int(Alien a) { return 2; } }
public class Gen<T> where T : Base
{
    public int Conv(T a) { int i = a; return i; }
    public bool Eq(T a, T b) { return a == b; }
    public int Idx(T a) { return a[0]; }
}
public class Chain<T, U> where U : T where T : Base
{
    public bool Eq(U a, U b) { return a == b; }
    public int Idx(U a) { return a[0]; }
}
public class Loose<T>
{
    public int Conv(T a) { return 0; }
    public bool Eq(T a, T b) { return false; }
}
public class OfAlien<T> where T : Alien
{
    public int Conv(T a) { int i = a; return i; }
}
public class Method
{
    public int Conv<T>(T a) where T : Child { int i = a; return i; }
}
public class Via<T> where T : IShape
{
    public int Idx(T a) { return a[0]; }
}
"#;

fn constrained_callers(marker: &str) -> Vec<String> {
    let Some(semantic) = compile(&[("C.cs", CONSTRAINED)], true) else {
        return Vec::new();
    };
    let path = Path::new("/p/C.cs");
    let symbol = semantic
        .call_hierarchy_item(path, at(CONSTRAINED, marker, 0), None)
        .expect("the member")
        .symbol;
    let mut from: Vec<String> = semantic
        .incoming_calls(symbol)
        .iter()
        .map(|call| format!("{}.{}", call.from.container, call.from.name))
        .collect();
    from.sort();
    from
}

/// A value of a type parameter has the members of what it is constrained to:
/// its conversion, `==` and indexer run where the body writes `T`, which
/// never names `Base`. A parameter constrained through another is one too;
/// a parameter with no such constraint, or another one, is not.
#[test]
fn a_member_reached_through_a_constraint_is_run_by_the_body() {
    assert_eq!(
        constrained_callers("operator int(Base b)"),
        vec!["Gen`1.Conv", "Method.Conv"]
    );
    assert_eq!(
        constrained_callers("==(Base a, Base b)"),
        vec!["Chain`2.Eq", "Gen`1.Eq"]
    );
    assert_eq!(
        constrained_callers("this[int i] { get { return i; } }"),
        vec!["Chain`2.Idx", "Gen`1.Idx"]
    );
    // Another class's conversion is for the parameter constrained to it.
    assert_eq!(
        constrained_callers("operator int(Alien a)"),
        vec!["OfAlien`1.Conv"]
    );
}

/// What a constraint to an interface runs is the interface's member.
#[test]
fn an_interface_constraint_runs_the_interfaces_indexer() {
    assert_eq!(
        constrained_callers("this[int i] { get; }"),
        vec!["Via`1.Idx"]
    );
}

const CONDITIONAL: &str = r#"public class Coll
{
    public override string ToString() { return "C"; }
    public override bool Equals(object o) { return false; }
    public override int GetHashCode() { return 1; }
    public string Foo() { return "f"; }
}
public class Other
{
    public override string ToString() { return "O"; }
}
public class Use
{
    void f1(Coll a) { var s = a.ToString(); }
    void f2(Coll a) { var s = a?.ToString(); }
    void f3(Coll a) { var s = a?.Foo(); }
    void f4(Coll a) { var s = a?.Equals(null); }
    void f5(Coll a) { var s = a?.GetHashCode(); }
    void f6(Coll a) { var s = a?.ToString().Length; }
    void f7(Coll a) { var s = a.GetHashCode(); }
    void f8(Coll a) { var s = a.Equals(a); }
    void f9(Coll a) { var s = object.Equals(a, a); }
    void g1(Other o) { var s = o?.ToString(); }
    void g2(object o) { var s = o?.ToString(); }
    void g3(Coll a, Other o) { var s = a?.Foo() + o?.ToString(); }
}
"#;

fn conditional_callers(marker: &str) -> Vec<String> {
    let Some(semantic) = compile(&[("C.cs", CONDITIONAL)], true) else {
        return Vec::new();
    };
    let path = Path::new("/p/C.cs");
    let symbol = semantic
        .call_hierarchy_item(path, at(CONDITIONAL, marker, 0), None)
        .expect("the member")
        .symbol;
    let mut from: Vec<String> = semantic
        .incoming_calls(symbol)
        .iter()
        .filter(|call| !call.through_base)
        .map(|call| call.from.name.clone())
        .collect();
    from.sort();
    from
}

/// `a?.M()` runs the member of the type of `a`, as `a.M()` does: an
/// override of `ToString`, `Equals` or `GetHashCode` among them, which the
/// binder records as the member of `object` on a conditional access. Another
/// type's override, and an `object`'s, are not run.
#[test]
fn a_conditional_access_runs_the_members_of_the_receiver() {
    assert_eq!(
        conditional_callers("ToString() { return \"C\"; }"),
        vec!["f1", "f2", "f6"]
    );
    assert_eq!(
        conditional_callers("Equals(object o) { return false; }"),
        vec!["f4", "f8"]
    );
    assert_eq!(
        conditional_callers("GetHashCode() { return 1; }"),
        vec!["f5", "f7"]
    );
    assert_eq!(conditional_callers("Foo() {"), vec!["f3", "g3"]);
    assert_eq!(
        conditional_callers("ToString() { return \"O\"; }"),
        vec!["g1", "g3"]
    );
}
