//! The errors and warnings an editor lists for a file: each one Roslyn would
//! report, with its code, its wording and the text it underlines — and, for
//! each, code that looks close to it and is fine, which must stay quiet.

use rustlyn_semantics::Compilation;
use rustlyn_syntax::{LanguageVersion, ParseOptions, parse, parse_with};
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

/// A statement list inside a method of a class.
fn in_method(body: &str) -> String {
    format!("using System;\nusing System.Collections.Generic;\nclass C {{ void M() {{ {body} }} }}")
}

/// A statement list inside a method with a `bool b` and an `int n` to
/// branch on.
fn with_flag(body: &str) -> String {
    format!("using System;\nclass C {{ void M(bool b, int n) {{ {body} }} }}")
}

fn assert_clean(source: &str) {
    let found = diagnose(source);
    assert!(found.is_empty(), "expected nothing, found {found:#?}");
}

// MARK: - names that do not exist

#[test]
fn a_missing_instance_member_is_cs1061_and_a_missing_static_one_cs0117() {
    assert_eq!(
        diagnose(&in_method("var s = \"a\"; var n = s.Nonesuch;")),
        [
            "CS1061 'Nonesuch': 'string' does not contain a definition for 'Nonesuch' and no accessible extension method 'Nonesuch' accepting a first argument of type 'string' could be found (are you missing a using directive or an assembly reference?)"
        ]
    );
    assert_eq!(
        codes(&in_method("var s = \"a\"; s.Nonesuch();")),
        ["CS1061"]
    );
    assert_eq!(
        diagnose(&in_method("Console.Nonesuch();")),
        ["CS0117 'Nonesuch': 'Console' does not contain a definition for 'Nonesuch'"]
    );
    assert_eq!(codes(&in_method("var x = string.Nonesuch;")), ["CS0117"]);
    assert_eq!(codes(&in_method("this.Nonesuch();")), ["CS1061"]);
}

#[test]
fn a_missing_method_called_by_its_name_alone_is_not_in_the_context() {
    assert_eq!(
        diagnose(&in_method("Nonesuch(1);")),
        ["CS0103 'Nonesuch': The name 'Nonesuch' does not exist in the current context"]
    );
}

#[test]
fn a_missing_type_in_a_signature_is_reported_where_it_is_written() {
    assert_eq!(
        diagnose("class C { Nonesuch field; Missing M(Absent a) => null; }"),
        [
            "CS0246 'Nonesuch': The type or namespace name 'Nonesuch' could not be found (are you missing a using directive or an assembly reference?)",
            "CS0246 'Missing': The type or namespace name 'Missing' could not be found (are you missing a using directive or an assembly reference?)",
            "CS0246 'Absent': The type or namespace name 'Absent' could not be found (are you missing a using directive or an assembly reference?)",
        ]
    );
    assert_eq!(codes("class C : Nonesuch { }"), ["CS0246"]);
    assert_eq!(codes("class C<T> where T : Nonesuch { }"), ["CS0246"]);
    assert_clean("class C<T, U> where T : notnull where U : unmanaged { }");
}

#[test]
fn a_generic_name_that_is_missing_reads_with_its_arity() {
    assert_eq!(
        diagnose("class C { Nonesuch<int, string> field; }"),
        [
            "CS0246 'Nonesuch<int, string>': The type or namespace name 'Nonesuch<,>' could not be found (are you missing a using directive or an assembly reference?)"
        ]
    );
}

#[test]
fn a_dotted_name_blames_the_part_that_is_missing() {
    assert_eq!(
        diagnose("class C { System.Nonesuch field; }"),
        [
            "CS0234 'Nonesuch': The type or namespace name 'Nonesuch' does not exist in the namespace 'System' (are you missing an assembly reference?)"
        ]
    );
    assert_eq!(
        diagnose("class C { class Inner { } C.Other field; }"),
        ["CS0426 'Other': The type name 'Other' does not exist in the type 'C'"]
    );
    assert_eq!(codes("class C { Nonesuch.Inner field; }"), ["CS0246"]);
    assert_eq!(
        codes(&in_method("var x = System.Nonesuch.Value;")),
        ["CS0234"]
    );
}

#[test]
fn a_generic_type_with_the_wrong_number_of_arguments_is_cs0305() {
    assert_eq!(
        diagnose("using System.Collections.Generic; class C { List<int, int> field; }"),
        ["CS0305 'List<int, int>': Using the generic type 'List<T>' requires 1 type arguments"]
    );
}

#[test]
fn an_attribute_that_does_not_exist_is_reported_under_both_names() {
    assert_eq!(codes("[Nonesuch] class C { }"), ["CS0246", "CS0246"]);
    assert_clean(
        "class MarkAttribute : System.Attribute { public MarkAttribute() { } public MarkAttribute(string s) { } } [Mark] class C { [MarkAttribute(\"x\")] void M() { } }",
    );
}

// MARK: - members against each other

#[test]
fn two_members_of_one_name_are_cs0102() {
    assert_eq!(
        diagnose("class C { int a; string a; }"),
        ["CS0102 'a': The type 'C' already contains a definition for 'a'"]
    );
    assert_eq!(
        codes("class C { int P { get; set; } void P() { } }"),
        ["CS0102"]
    );
    assert_clean("class C { int a; int b; void M() { } void M(int x) { } }");
}

#[test]
fn two_methods_with_the_same_parameters_are_cs0111() {
    assert_eq!(
        diagnose("class C { void M(int a) { } void M(int b) { } }"),
        ["CS0111 'M': Type 'C' already defines a member called 'M' with the same parameter types"]
    );
    assert_eq!(codes("class C { C() { } C() { } }"), ["CS0111"]);
    assert_eq!(
        codes("class C { void M<T>(T a) { } void M<U>(U b) { } }"),
        ["CS0111"]
    );
    assert_clean(
        "class C { void M(int a) { } void M(long a) { } void M(ref int a) { } void M<T>(int a) { } }",
    );
}

// MARK: - what a type inherits

#[test]
fn a_missing_interface_member_is_cs0535_on_the_interface() {
    assert_eq!(
        diagnose("interface IShape { int Area(); } class Square : IShape { }"),
        ["CS0535 'IShape': 'Square' does not implement interface member 'IShape.Area()'"]
    );
    assert_eq!(
        codes("interface IShape { int Sides { get; } } class Square : IShape { }"),
        ["CS0535"]
    );
    assert_eq!(
        codes("interface IA { void M(); } interface IB : IA { } class C : IB { }"),
        ["CS0535"]
    );
    assert_eq!(
        diagnose(
            "interface I<T> { void Take(T item); } class C : I<string> { public void Take(int item) { } }"
        ),
        ["CS0535 'I<string>': 'C' does not implement interface member 'I<string>.Take(string)'"]
    );
}

#[test]
fn an_implemented_interface_is_quiet() {
    assert_clean(
        "interface IShape { int Area(); } class Square : IShape { public int Area() => 4; }",
    );
    assert_clean(
        "interface IShape { int Area(); } class Square : IShape { int IShape.Area() => 4; }",
    );
    assert_clean(
        "interface I<T> { void Take(T item); } class C : I<string> { public void Take(string item) { } }",
    );
    assert_clean(
        "interface IShape { int Area(); } class Base { public int Area() => 1; } class Square : Base, IShape { }",
    );
    assert_clean("interface IShape { int Area() => 0; } class Square : IShape { }");
    assert_clean(
        "interface IShape { int Sides { get; } event System.Action Moved; } class Square : IShape { public int Sides => 4; public event System.Action Moved; }",
    );
    assert_clean("interface I { void M<T>(T x); } class C : I { public void M<U>(U x) { } }");
    assert_clean("interface I { static abstract int Make(); } class C { }");
    assert_clean("abstract class C : System.IDisposable { public abstract void Dispose(); }");
}

#[test]
fn an_implementation_with_the_wrong_return_type_is_cs0738() {
    assert_eq!(
        diagnose(
            "interface IShape { int Area(); } class Square : IShape { public long Area() => 4; }"
        ),
        [
            "CS0738 'IShape': 'Square' does not implement interface member 'IShape.Area()'. 'Square.Area()' cannot implement 'IShape.Area()' because it does not have the matching return type of 'int'."
        ]
    );
}

#[test]
fn an_abstract_member_left_open_is_cs0534_on_the_class() {
    assert_eq!(
        diagnose("abstract class Shape { public abstract int Area(); } class Square : Shape { }"),
        ["CS0534 'Square': 'Square' does not implement inherited abstract member 'Shape.Area()'"]
    );
    assert_eq!(
        diagnose(
            "abstract class Shape { public abstract int Sides { get; } } class Square : Shape { }"
        ),
        [
            "CS0534 'Square': 'Square' does not implement inherited abstract member 'Shape.Sides.get'"
        ]
    );
    assert_clean(
        "abstract class Shape { public abstract int Area(); } class Square : Shape { public override int Area() => 4; }",
    );
    assert_clean(
        "abstract class Shape { public abstract int Area(); } abstract class Quad : Shape { } class Square : Quad { public override int Area() => 4; }",
    );
    assert_clean(
        "abstract class Shape { public abstract int Area(); } abstract class Quad : Shape { }",
    );
    assert_clean(
        "abstract class Shape<T> { public abstract T Make(T seed); } class Squares : Shape<int> { public override int Make(int seed) => seed; }",
    );
}

#[test]
fn an_override_needs_something_virtual_to_override() {
    assert_eq!(
        diagnose("class Shape { } class Square : Shape { public override int Area() => 4; }"),
        ["CS0115 'Area': 'Square.Area()': no suitable method found to override"]
    );
    assert_eq!(
        diagnose(
            "class Shape { public int Area() => 1; } class Square : Shape { public override int Area() => 4; }"
        ),
        [
            "CS0506 'Area': 'Square.Area()': cannot override inherited member 'Shape.Area()' because it is not marked virtual, abstract, or override"
        ]
    );
    assert_eq!(
        codes(
            "class A { public virtual void M() { } } class B : A { public sealed override void M() { } } class C : B { public override void M() { } }"
        ),
        ["CS0239"]
    );
    assert_clean(
        "class Shape { public virtual int Area() => 1; } class Square : Shape { public override int Area() => 4; public override string ToString() => \"\"; }",
    );
    assert_clean(
        "struct S { public override string ToString() => \"\"; public override int GetHashCode() => 1; }",
    );
}

#[test]
fn a_member_that_hides_one_it_inherits_is_warned_about() {
    assert_eq!(
        diagnose(
            "class Shape { public int Area() => 1; } class Square : Shape { public int Area() => 4; }"
        ),
        [
            "CS0108 'Area': 'Square.Area()' hides inherited member 'Shape.Area()'. Use the new keyword if hiding was intended."
        ]
    );
    assert_eq!(
        diagnose(
            "class Shape { public virtual int Area() => 1; } class Square : Shape { public int Area() => 4; }"
        ),
        [
            "CS0114 'Area': 'Square.Area()' hides inherited member 'Shape.Area()'. To make the current member override that implementation, add the override keyword. Otherwise add the new keyword."
        ]
    );
    assert_eq!(
        codes("class A { public int X; } class B : A { public int X; }"),
        ["CS0108"]
    );
    assert_eq!(
        codes("class C { public string ToString() => \"\"; }"),
        ["CS0114"]
    );
    assert_clean(
        "class Shape { public int Area() => 1; } class Square : Shape { public new int Area() => 4; public int Area(int scale) => scale; }",
    );
    assert_clean("class A { private int x; } class B : A { private int x; }");
}

#[test]
fn an_abstract_member_of_a_concrete_class_is_cs0513() {
    assert_eq!(
        codes("class Shape { public abstract int Area(); }"),
        ["CS0513"]
    );
}

// MARK: - control flow

#[test]
fn a_method_that_can_run_off_its_end_is_cs0161() {
    assert_eq!(
        diagnose("class C { int M(bool b) { if (b) return 1; } }"),
        ["CS0161 'M': 'C.M(bool)': not all code paths return a value"]
    );
    assert_eq!(
        codes("class C { int M(int x) { switch (x) { case 1: return 1; } } }"),
        ["CS0161"]
    );
    assert_eq!(
        codes("class C { int M(int x) { while (x > 0) { return 1; } } }"),
        ["CS0161"]
    );
    assert_eq!(
        diagnose("class C { int P { get { } } }"),
        ["CS0161 'get': 'C.P.get': not all code paths return a value"]
    );
    assert_eq!(
        codes("class C { void M() { int Local() { } Local(); } }"),
        ["CS0161"]
    );
    assert_eq!(
        codes("using System; class C { void M() { Func<int> f = () => { }; f(); } }"),
        ["CS1643"]
    );
}

#[test]
fn a_method_that_returns_on_every_path_is_quiet() {
    assert_clean("class C { int M(bool b) { if (b) return 1; else return 2; } }");
    assert_clean("class C { int M(bool b) { if (b) return 1; throw new System.Exception(); } }");
    assert_clean("class C { int M() { while (true) { } } }");
    assert_clean("class C { int M() { for (;;) { } } }");
    assert_clean(
        "class C { int M(int x) { switch (x) { case 1: return 1; default: return 2; } } }",
    );
    assert_clean("class C { int M(int x) { try { return 1; } finally { } } }");
    assert_clean("class C { int M(int x) { try { return 1; } catch { throw; } } }");
    assert_clean("class C { int M() { do { return 1; } while (true); } }");
    assert_clean("class C { void M(bool b) { if (b) return; } }");
    assert_clean("class C { int M() => 1; int P => 2; int Q { get => 3; } }");
    assert_clean(
        "using System.Collections.Generic; class C { IEnumerable<int> M() { yield return 1; } }",
    );
    assert_clean("abstract class C { public abstract int M(); }");
    assert_clean(
        "using System; class C { void M() { Func<int> f = () => 1; Action a = () => { }; f(); a(); } }",
    );
}

#[test]
fn a_loop_left_by_break_reaches_its_end() {
    assert_eq!(
        codes("class C { int M() { while (true) { break; } } }"),
        ["CS0161"]
    );
    assert_clean(
        "class C { int M(int x) { while (true) { switch (x) { case 1: break; default: break; } } } }",
    );
}

#[test]
fn code_after_a_return_is_unreachable() {
    assert_eq!(
        diagnose(&in_method(
            "return; Console.WriteLine(1); Console.WriteLine(2);"
        )),
        ["CS0162 'Console': Unreachable code detected"]
    );
    assert_eq!(
        codes(&in_method("while (true) { } int x = 1; x++;")),
        ["CS0162"]
    );
    assert_eq!(
        codes(&in_method("if (false) { Console.WriteLine(1); }")),
        ["CS0162"]
    );
    // A comparison of constants is a constant (§12.25), named ones too.
    assert_eq!(
        codes(
            "using System;\nclass C { const int A = 10000; const int B = 1000; const string S = \"s\";\n\
             void M() { if (A % B != 0) { Console.WriteLine(1); } if (!(A > B) || S == null) { Console.WriteLine(2); } if (A >= B && S != \"t\") { Console.WriteLine(3); } } }"
        ),
        ["CS0162", "CS0162"]
    );
    // A local function after the return is only declared there.
    assert_clean(&in_method("return; void Local() { } "));
    assert_clean(&in_method(
        "int x = 1; if (x > 0) return; Console.WriteLine(x);",
    ));
}

// MARK: - locals

#[test]
fn a_local_never_used_is_cs0168() {
    assert_eq!(
        diagnose(&in_method("int x;")),
        ["CS0168 'x': The variable 'x' is declared but never used"]
    );
    assert_eq!(
        codes(&in_method("try { } catch (Exception e) { }")),
        ["CS0168"]
    );
}

#[test]
fn a_local_only_ever_given_constants_is_cs0219() {
    assert_eq!(
        diagnose(&in_method("int x = 1;")),
        ["CS0219 'x': The variable 'x' is assigned but its value is never used"]
    );
    assert_eq!(codes(&in_method("string s = \"a\"; s = null;")), ["CS0219"]);
    assert_eq!(codes(&in_method("object o = null;")), ["CS0219"]);
    assert_eq!(codes(&in_method("int x; x = 2;")), ["CS0219"]);
}

#[test]
fn a_local_that_is_read_or_given_a_computed_value_is_quiet() {
    assert_clean(&in_method("int x = 1; Console.WriteLine(x);"));
    assert_clean(&in_method("var x = Console.ReadLine();"));
    assert_clean(&in_method("object o = new object();"));
    assert_clean(&in_method("int x = 0; x++;"));
    assert_clean(&in_method("int x = 0; x += 2;"));
    assert_clean(&in_method("int x; int.TryParse(\"1\", out x);"));
    assert_clean(&in_method("int x = 1; Func<int> f = () => x; f();"));
    assert_clean(&in_method("int? x = 1;"));
    assert_clean(&in_method("const int x = 1;"));
    assert_clean(&in_method("foreach (var item in new int[0]) { }"));
    assert_clean(&in_method("try { } catch (Exception) { }"));
    assert_clean(&in_method("int x = 1; var s = nameof(x);"));
    // A struct made from a literal through its own operator is a call.
    assert_clean(
        "struct Big { public static implicit operator Big(int v) => default; } class C { void M() { Big b = 0; } }",
    );
}

#[test]
fn a_local_read_before_it_is_surely_assigned_is_cs0165() {
    assert_eq!(
        diagnose(&with_flag("int x; Console.WriteLine(x);")),
        ["CS0165 'x': Use of unassigned local variable 'x'"]
    );
    assert_eq!(
        codes(&with_flag("int x; if (b) x = 1; Console.WriteLine(x);")),
        ["CS0165"]
    );
    // Reported once, at the first read.
    assert_eq!(
        codes(&with_flag("int x; x++; Console.WriteLine(x);")),
        ["CS0165"]
    );
    assert_eq!(codes(&with_flag("int x = x + 1;")), ["CS0165"]);
    // An `out` argument is assigned once the call returns, not before the
    // arguments after it are evaluated.
    assert_eq!(
        codes(
            "class C { static void Two(out int a, int b) { a = b; } void M() { int x; Two(out x, x); } }"
        ),
        ["CS0165"]
    );
    // A pattern's variable is assigned only where the pattern matched.
    assert_eq!(
        codes(&with_flag(
            "object o = 1; if (o is int i || o == null) Console.WriteLine(i);"
        )),
        ["CS0165"]
    );
    // What a lambda assigns counts for nothing outside it.
    assert_eq!(
        codes(&with_flag(
            "int x; Action a = () => x = 1; a(); Console.WriteLine(x);"
        )),
        ["CS0165"]
    );
}

#[test]
fn a_local_assigned_on_every_path_is_not_cs0165() {
    assert_clean(&with_flag(
        "int x; if (b) x = 1; else x = 2; Console.WriteLine(x);",
    ));
    assert_clean(&with_flag(
        "int x; while (true) { x = 1; break; } Console.WriteLine(x);",
    ));
    assert_clean(&with_flag(
        "int x; for (;;) { if (b) { x = 1; break; } } Console.WriteLine(x);",
    ));
    assert_clean(&with_flag(
        "int x; do { x = 1; } while (x < 0); Console.WriteLine(x);",
    ));
    assert_clean(&with_flag(
        "int x; if (int.TryParse(\"1\", out x) && x > 0) { }",
    ));
    assert_clean(&with_flag(
        "object o = 1; if (!(o is int i)) return; Console.WriteLine(i);",
    ));
    assert_clean(&with_flag(
        "object o = 1; if (o is not int i) return; Console.WriteLine(i);",
    ));
    assert_clean(&with_flag(
        "int x; try { x = 1; } catch (Exception) { x = 2; } Console.WriteLine(x);",
    ));
    assert_clean(&with_flag(
        "int x; try { } finally { x = 1; } Console.WriteLine(x);",
    ));
    assert_clean(&with_flag(
        "int x; switch (n) { case 1: x = 1; break; default: x = 2; break; } Console.WriteLine(x);",
    ));
    // Code nothing reaches reads nothing.
    assert_eq!(
        codes(&with_flag(
            "int x; if (false) Console.WriteLine(x); x = 1; Console.WriteLine(x);"
        )),
        ["CS0162"]
    );
    assert_clean(&with_flag("int x; x = 1; Func<int> f = () => x; f();"));
    // A local function that assigns a local may be what assigns it.
    assert_clean(&with_flag(
        "int x; void Set() { x = 1; } Set(); Console.WriteLine(x);",
    ));
    // A struct is assigned field by field as well as whole.
    assert_clean(
        "struct P { public int X, Y; } class C { void M() { P p; p.X = 1; p.Y = 2; System.Console.WriteLine(p); } }",
    );
    // A struct with no fields has nothing to assign.
    assert_clean("struct E { } class C { void M() { E e; System.Console.WriteLine(e); } }");
}

#[test]
fn a_variable_declared_further_on_in_the_same_statement_is_cs0841() {
    let helper = "static bool Take(out int x) { x = 1; return true; } ";
    assert_eq!(
        diagnose(&format!(
            "class C {{ {helper}void M(bool b) {{ if (x > 0 && Take(out var x)) {{ }} }} }}"
        )),
        ["CS0841 'x': Cannot use local variable 'x' before it is declared"]
    );
    assert_eq!(
        codes("class C { void M(object o) { if (i > 0 && o is int i) { } } }"),
        ["CS0841"]
    );
    // A `var` local cannot be used to work out its own type.
    assert_eq!(codes("class C { void M() { var x = x + 1; } }"), ["CS0841"]);
    // A variable in a loop's condition is not in scope after the loop.
    assert_eq!(
        codes(&format!(
            "class C {{ {helper}void M() {{ while (Take(out var x)) {{ }} System.Console.WriteLine(x); }} }}"
        )),
        ["CS0103"]
    );
}

#[test]
fn an_out_parameter_must_be_assigned_before_the_method_returns() {
    assert_eq!(
        diagnose("class C { void M(out int a) { } }"),
        [
            "CS0177 'M': The out parameter 'a' must be assigned to before control leaves the current method"
        ]
    );
    assert_eq!(
        codes("class C { void M(bool b, out int a) { if (b) return; a = 1; } }"),
        ["CS0177"]
    );
    assert_eq!(
        diagnose("class C { void M(out int a) { a = a + 1; } }"),
        ["CS0269 'a': Use of unassigned out parameter 'a'"]
    );
    assert_clean(
        "class C { void A(out int a) { a = 1; } void B(out int a) { A(out a); } void D(out int a) { throw null; } bool E(out int a) { try { return true; } finally { a = 1; } } static extern void F(out int a); }",
    );
}

#[test]
fn an_extern_local_function_needs_no_return() {
    assert_clean("class C { void M() { static extern int Call(); } }");
}

#[test]
fn a_tuple_and_its_value_tuple_implement_each_other() {
    assert_clean(
        "namespace System { public struct ValueTuple<T1, T2> { } } namespace N { using Pair = System.ValueTuple<int, string>; interface I<T> { I<T> Make(); } class C : I<Pair> { public I<(int, string)> Make() => null; } }",
    );
}

// MARK: - calls and creation

#[test]
fn a_constructor_nothing_takes_is_cs1729_or_cs7036() {
    assert_eq!(
        diagnose(
            "class P { public P(int x, int y) { } public P() { } } class C { object M() => new P(1); }"
        ),
        ["CS1729 'P': 'P' does not contain a constructor that takes 1 arguments"]
    );
    assert_eq!(
        diagnose("class P { public P(int x, int y) { } } class C { object M() => new P(1); }"),
        [
            "CS7036 'P': There is no argument given that corresponds to the required parameter 'y' of 'P.P(int, int)'"
        ]
    );
    assert_eq!(
        codes("class B { public B(int x) { } } class D : B { public D() : base() { } }"),
        ["CS7036"]
    );
    assert_clean("class P { public P(int x, int y = 2) { } } class C { object M() => new P(1); }");
    assert_clean("struct S { public S(int x) { } } class C { object M() => new S(); }");
}

#[test]
fn a_call_with_too_few_arguments_names_the_missing_one() {
    assert_eq!(
        diagnose("class C { void Take(int a, int b) { } void M() { Take(1); } }"),
        [
            "CS7036 'Take': There is no argument given that corresponds to the required parameter 'b' of 'C.Take(int, int)'"
        ]
    );
    assert_eq!(
        codes("class C { void Take(int a) { } void M() { Take(1, 2); } }"),
        ["CS1501"]
    );
}

#[test]
fn a_wrong_argument_is_reported_on_the_argument() {
    assert_eq!(
        diagnose("class C { void Take(int a) { } void M() { Take(\"s\"); } }"),
        ["CS1503 '\"s\"': Argument 1: cannot convert from 'string' to 'int'"]
    );
}

#[test]
fn an_abstract_type_or_an_interface_cannot_be_made() {
    assert_eq!(
        diagnose("abstract class Shape { } class C { object M() => new Shape(); }"),
        [
            "CS0144 'new Shape()': Cannot create an instance of the abstract type or interface 'Shape'"
        ]
    );
    assert_eq!(
        codes("interface IShape { } class C { object M() => new IShape(); }"),
        ["CS0144"]
    );
}

// MARK: - static and instance

#[test]
fn an_instance_member_from_a_static_one_needs_an_object() {
    assert_eq!(
        diagnose("class C { int count; static int M() => count; }"),
        [
            "CS0120 'count': An object reference is required for the non-static field, method, or property 'C.count'"
        ]
    );
    assert_eq!(
        codes("class C { void Run() { } static void M() { Run(); } }"),
        ["CS0120"]
    );
    assert_eq!(
        codes("class C { public int Count; } class D { static int M() => C.Count; }"),
        ["CS0120"]
    );
    assert_eq!(
        codes("class C { public void Run() { } } class D { static void M() { C.Run(); } }"),
        ["CS0120"]
    );
    assert_clean(
        "class C { static int count; int other; static int M() => count; int N() => other + count; }",
    );
    // `Color Color`: the property and its type share a name.
    assert_clean(
        "enum Color { Red } class C { Color Color { get; set; } static Color M() => Color.Red; void N() { Color = Color.Red; } }",
    );
}

#[test]
fn a_static_member_through_an_instance_is_cs0176() {
    assert_eq!(
        codes("class C { public static int Count; } class D { int M(C c) => c.Count; }"),
        ["CS0176"]
    );
    assert_eq!(
        codes("class C { public static void Run() { } } class D { void M(C c) { c.Run(); } }"),
        ["CS0176"]
    );
}

// MARK: - conversions and assignments

#[test]
fn a_conversion_a_cast_would_make_is_cs0266() {
    assert_eq!(
        diagnose(&in_method(
            "long big = 1; int small = big; Console.WriteLine(small);"
        )),
        [
            "CS0266 'big': Cannot implicitly convert type 'long' to 'int'. An explicit conversion exists (are you missing a cast?)"
        ]
    );
    assert_eq!(
        codes(&in_method(
            "object o = 1; string s = o; Console.WriteLine(s);"
        )),
        ["CS0266"]
    );
    assert_eq!(
        codes(&in_method("string s = 1; Console.WriteLine(s);")),
        ["CS0029"]
    );
}

#[test]
fn a_read_only_target_cannot_be_assigned() {
    assert_eq!(
        diagnose("class C { int P => 1; void M() { P = 2; } }"),
        ["CS0200 'P': Property or indexer 'C.P' cannot be assigned to -- it is read only"]
    );
    assert_eq!(
        codes("class C { readonly int f; void M() { f = 2; } }"),
        ["CS0191"]
    );
    assert_eq!(
        codes("class C { static readonly int f; void M() { f = 2; } }"),
        ["CS0198"]
    );
    assert_eq!(
        codes("class C { const int f = 1; void M() { f = 2; } }"),
        ["CS0131"]
    );
    assert_eq!(
        codes("class C { int F() => 1; void M() { F() = 2; } }"),
        ["CS0131"]
    );
    assert_clean(
        "class C { readonly int f; int P { get; } static readonly int s; C() { f = 1; P = 2; } static C() { s = 3; } }",
    );
}

#[test]
fn var_needs_a_value_with_a_type() {
    assert_eq!(
        diagnose(&in_method("var x;")),
        ["CS0818 'x': Implicitly-typed variables must be initialized"]
    );
    assert_eq!(
        diagnose(&in_method("var x = null;")),
        ["CS0815 'x = null': Cannot assign <null> to an implicitly-typed variable"]
    );
}

#[test]
fn await_needs_an_async_method() {
    // Something with the awaitable pattern; the core library here has no
    // `Task`.
    let job = "class Job { public Waiter GetAwaiter() => new Waiter(); } class Waiter { public bool IsCompleted => true; public int GetResult() => 1; }";
    assert_eq!(
        diagnose(&format!(
            "{job} class C {{ int M(Job j) {{ return await j; }} }}"
        )),
        [
            "CS4032 'await j': The 'await' operator can only be used within an async method. Consider marking this method with the 'async' modifier and changing its return type to 'Task<int>'."
        ]
    );
    assert_eq!(
        codes(&format!(
            "{job} class C {{ void Use(int x) {{ }} void M(Job j) {{ Use(await j); }} }}"
        )),
        ["CS4033"]
    );
    assert_eq!(
        codes(&format!(
            "using System; {job} class C {{ void M(Job j) {{ Func<int> f = () => await j; f(); }} }}"
        )),
        ["CS4034"]
    );
}

// MARK: - local scopes

#[test]
fn a_local_hiding_one_around_it_is_cs0136() {
    assert_eq!(
        diagnose(&in_method(
            "int a = 1; { int a = 2; Console.WriteLine(a); } Console.WriteLine(a);"
        )),
        [
            "CS0136 'a': A local or parameter named 'a' cannot be declared in this scope because that name is used in an enclosing local scope to define a local or parameter"
        ]
    );
    assert_eq!(
        codes("class C { void M(int a) { int a = 1; System.Console.WriteLine(a); } }"),
        ["CS0136"]
    );
    assert_eq!(
        codes(&in_method("int a = 1; int a = 2; Console.WriteLine(a);")),
        ["CS0128"]
    );
    assert_clean(&in_method(
        "{ int a = 1; Console.WriteLine(a); } { int a = 2; Console.WriteLine(a); }",
    ));
    assert_clean("class C { void M(int a) { System.Func<int, int> f = a => a; f(a); } }");
}

#[test]
fn a_local_used_before_its_declaration_is_cs0841() {
    assert_eq!(
        diagnose(&in_method(
            "Console.WriteLine(x); int x = 1; Console.WriteLine(x);"
        )),
        ["CS0841 'x': Cannot use local variable 'x' before it is declared"]
    );
}

// MARK: - accessibility

#[test]
fn a_private_member_of_another_type_is_cs0122() {
    assert_eq!(
        diagnose("class A { private int secret; } class B { int M(A a) => a.secret; }"),
        ["CS0122 'secret': 'A.secret' is inaccessible due to its protection level"]
    );
    assert_eq!(
        codes("class A { void Hidden() { } } class B { void M(A a) { a.Hidden(); } }"),
        ["CS0122"]
    );
    assert_eq!(
        codes("class A { private int secret; } class B : A { int M() => secret; }"),
        ["CS0122"]
    );
    assert_clean(
        "class A { private int secret; protected int shared; int Own(A other) => other.secret; class Inner { int M(A a) => a.secret; } } class B : A { int M() => shared; }",
    );
}

#[test]
fn an_attribute_aimed_where_the_declaration_has_nothing_is_warned_about() {
    let attribute = "class A : System.Attribute { } ";
    assert_eq!(
        diagnose(&format!("{attribute}[return: A] class C {{ }}")),
        [
            "CS0657 'return': 'return' is not a valid attribute location for this declaration. Valid attribute locations for this declaration are 'type'. All attributes in this block will be ignored."
        ]
    );
    assert_eq!(
        diagnose(&format!(
            "{attribute}class C {{ [delegate: A] void M() {{ }} }}"
        )),
        [
            "CS0658 'delegate': 'delegate' is not a recognized attribute location. Valid attribute locations for this declaration are 'method, return'. All attributes in this block will be ignored."
        ]
    );
    assert_clean(&format!(
        "{attribute}[type: A] class C {{ [return: A] [method: A] int M() => 0; [field: A] int f; int P {{ get; [param: A] set; }} }}"
    ));
}

#[test]
fn a_pointer_outside_an_unsafe_context_is_cs0214() {
    assert_eq!(
        diagnose("class C { int M(int* p) => 0; }"),
        ["CS0214 'int*': Pointers and fixed size buffers may only be used in an unsafe context"]
    );
    assert_eq!(
        codes("class C { void M(int x) { var p = &x; } }"),
        ["CS0214"]
    );
    assert_clean(
        "unsafe class C { int* p; } class D { unsafe int* q; unsafe void M(int x) { var p = &x; *p = 1; } void N(int x) { unsafe { int* p = &x; } } }",
    );
}

#[test]
fn in_the_preview_only_reading_through_a_pointer_needs_an_unsafe_context() {
    let preview = |source: &str| {
        let options = ParseOptions::default().with_language_version(LanguageVersion::Preview);
        let compilation = Compilation::create(vec![parse_with(
            SourceText::new("Program.cs", source),
            &options,
        )]);
        compilation
            .semantic_diagnostics()
            .into_iter()
            .map(|entry| {
                let span = entry.diagnostic.span();
                format!(
                    "{} '{}'",
                    entry.diagnostic.code(),
                    &source[span.start() as usize..span.end() as usize]
                )
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(preview("class C { int M(int* p) => *p; }"), ["CS9360 '*'"]);
    assert_eq!(
        preview("class C { int M(int* p) => p[1]; }"),
        ["CS9360 '['"]
    );
    assert!(preview("class C { int* p; void M(int x) { var q = &x; } }").is_empty());
}

#[test]
fn an_expression_that_only_computes_a_value_is_no_statement() {
    assert_eq!(
        diagnose(&with_flag("n + 1;")),
        [
            "CS0201 'n + 1': Only assignment, call, increment, decrement, await, and new object expressions can be used as a statement"
        ]
    );
    assert_eq!(codes(&with_flag("n;")), ["CS0201"]);
    assert_eq!(codes(&with_flag("nameof(n);")), ["CS0201"]);
    // One that did not bind has been complained about already.
    assert_eq!(codes(&with_flag("nope + 1;")), ["CS0103"]);
    assert_clean(&with_flag(
        "n++; --n; n = 2; n += 3; M(b, n); new object(); Action a = null; a?.Invoke();",
    ));
}

#[test]
fn a_declaration_as_the_body_of_an_if_is_cs1023() {
    assert_eq!(
        diagnose(&with_flag("if (b) int x = 1;")),
        [
            "CS1023 'int x = 1;': Embedded statement cannot be a declaration or labeled statement",
            "CS0219 'x': The variable 'x' is assigned but its value is never used"
        ]
    );
}

#[test]
fn a_stray_semicolon_after_an_if_is_warned_about() {
    assert_eq!(
        diagnose(&with_flag("if (b); n = 1;")),
        ["CS0642 ';': Possible mistaken empty statement"]
    );
    // A loop may well have nothing to do; only a block after it is
    // suspicious.
    assert_clean(&with_flag("while (n-- > 0); n = 1;"));
    assert_eq!(codes(&with_flag("while (n-- > 0); { n = 1; }")), ["CS0642"]);
}

#[test]
fn an_attribute_argument_must_be_a_constant() {
    let attribute = "class A : System.Attribute { public A(object o) { } public A(int[] a) { } } ";
    assert_eq!(
        diagnose(&format!(
            "{attribute}class C {{ [A(new object())] void M() {{ }} }}"
        )),
        [
            "CS0182 'new object()': An attribute argument must be a constant expression, typeof expression or array creation expression of an attribute parameter type"
        ]
    );
    assert_eq!(
        codes(&format!(
            "{attribute}class C {{ static readonly int F = 1; [A(F)] void M() {{ }} }}"
        )),
        ["CS0182"]
    );
    // What goes wrong inside the arguments is said too.
    assert_eq!(
        codes(&format!(
            "{attribute}class C {{ [A(nope)] void M() {{ }} }}"
        )),
        ["CS0103"]
    );
    assert_clean(&format!(
        "{attribute}enum E {{ P, Q }} class C {{ const int K = 2; [A(K + 1)] [A(E.P | E.Q)] [A(typeof(int))] [A(new int[] {{ 1, 2 }})] [A(\"a\" + \"b\")] [A(nameof(M))] [A(null)] void M() {{ }} }}"
    ));
}

#[test]
fn a_field_initializer_is_bound_for_what_it_gets_wrong() {
    assert_eq!(
        diagnose("class C { int f = nope; }"),
        ["CS0103 'nope': The name 'nope' does not exist in the current context"]
    );
    assert_eq!(codes("class C { static int a = 1, b = nope; }"), ["CS0103"]);
}

#[test]
fn coalescing_a_value_that_cannot_be_null_is_cs0019() {
    assert_eq!(
        diagnose(&with_flag("var a = n ?? 1;")),
        ["CS0019 'n ?? 1': Operator '??' cannot be applied to operands of type 'int' and 'int'"]
    );
    assert_eq!(codes(&with_flag("n ??= 1;")), ["CS0019"]);
    assert_clean(&with_flag(
        "int? m = null; var a = m ?? 1; string s = null; s ??= \"\"; m ??= 2;",
    ));
}

#[test]
fn a_struct_without_equality_is_not_compared_with_null() {
    // `NanoProfiler.MediumGroup == null` where the group is a struct with no
    // `==`: there is no operator to lift, so the comparison is CS0019 — the
    // lifted one a number, an enum or a struct declaring `==` has warns that
    // it is always false at most.
    let declarations = "struct S { public int X; } \
        struct E { public static bool operator ==(E a, E b) => true; public static bool operator !=(E a, E b) => false; public override bool Equals(object o) => true; public override int GetHashCode() => 0; } \
        enum K { A } \
        record struct R(int X); \
        static class G { public static S Group; } ";
    assert_eq!(
        diagnose(&format!(
            "{declarations}class C {{ void M(S s) {{ var a = s == null; var b = null != G.Group; }} }}"
        )),
        [
            "CS0019 's == null': Operator '==' cannot be applied to operands of type 'S' and '<null>'",
            "CS0019 'null != G.Group': Operator '!=' cannot be applied to operands of type '<null>' and 'S'",
        ]
    );
    assert_eq!(
        codes(&format!(
            "{declarations}class C {{ void M((int, int) t) {{ var a = t == null; }} }}"
        )),
        ["CS0019"]
    );
    for fine in [
        "e == null",
        "r != null",
        "s.X == null",
        "k == null",
        "(S?)s == null",
    ] {
        let found = codes(&format!(
            "{declarations}class C {{ void M(S s, E e, K k, R r) {{ var a = {fine}; }} }}"
        ));
        assert!(
            found.iter().all(|code| code == "CS0472"),
            "{fine}: {found:?}"
        );
    }
}

#[test]
fn an_enum_takes_only_numbers_its_underlying_type_holds() {
    let declarations = "enum E : short { A, B } ";
    assert_eq!(
        diagnose(&format!(
            "{declarations}class C {{ void M(E x, int i) {{ var a = x - i; }} }}"
        )),
        ["CS0019 'x - i': Operator '-' cannot be applied to operands of type 'E' and 'int'"]
    );
    // A constant that fits is fine, and a constant zero of any integral
    // type is a value of the enum itself.
    assert_clean(&format!(
        "{declarations}class C {{ void M(E x, short s) {{ var a = x - 1; var b = x + s; var c = 1 + x; var d = (long)0 - x; }} }}"
    ));
}

#[test]
fn a_using_of_something_that_cannot_be_disposed_is_cs1674() {
    let declarations = "struct S { } class R : System.IDisposable { public void Dispose() { } } ";
    assert_eq!(
        diagnose(&format!(
            "{declarations}class C {{ void M() {{ using (S s = new S()) {{ }} }} }}"
        )),
        [
            "CS1674 'S s = new S()': 'S': type used in a using statement must implement 'System.IDisposable'."
        ]
    );
    assert_eq!(
        codes(&format!(
            "{declarations}class C {{ void M() {{ using var s = new S(); }} }}"
        )),
        ["CS1674"]
    );
    assert_clean(&format!(
        "{declarations}class C {{ void M<T>(T t) where T : System.IDisposable {{ using (var r = new R()) {{ }} using var q = new R(); using (t) {{ }} }} }}"
    ));
}

#[test]
fn object_is_no_constraint() {
    assert_eq!(
        diagnose("class C<T> where T : object { }"),
        ["CS0702 'object': Constraint cannot be special class 'object'"]
    );
    assert_clean(
        "class C<T> where T : class { } interface I { } class D<T> where T : I, new() { }",
    );
}

#[test]
fn a_default_parameter_value_must_be_a_constant() {
    assert_eq!(
        diagnose("class C { static int p = 1; void M(int x = p) { } }"),
        ["CS1736 'p': Default parameter value for 'x' must be a compile-time constant"]
    );
    assert_eq!(codes("class C { void M(C c = new C()) { } }"), ["CS1736"]);
    assert_clean(
        "struct S { } class C { const int K = 2; void M(S s = new S(), int k = K + 1, string t = null, object o = default, S w = default(S)) { } }",
    );
}

#[test]
fn a_modifier_written_twice_is_cs1004() {
    assert_eq!(
        diagnose("public public class C { }"),
        ["CS1004 'public': Duplicate 'public' modifier"]
    );
    assert_eq!(
        codes("class C { public int R { private private get; set; } }"),
        ["CS1004"]
    );
    assert_clean(
        "public static class C { public static readonly int F = 1; private protected static void M() { } }",
    );
}

#[test]
fn a_property_with_no_getter_is_not_read() {
    assert_eq!(
        diagnose("class C { int P { set { } } int M(C c) => c.P; }"),
        [
            "CS0154 'c.P': The property or indexer 'C.P' cannot be used in this context because it lacks the get accessor"
        ]
    );
    assert_eq!(
        codes("class C { int P { set { } } void M(C c) { c.P += 1; } }"),
        ["CS0154"]
    );
    assert_clean(
        "class C { int P { set { } } int this[int i] { set { } } void M(C c) { c.P = 1; this[0] = 2; var o = new C { P = 3 }; } }",
    );
}

#[test]
fn a_var_given_something_with_no_type_of_its_own_is_cs8917() {
    assert_eq!(
        diagnose("class C { void M() { var f = x => x; } }"),
        ["CS8917 'x => x': The delegate type could not be inferred."]
    );
    // Calling a variable that holds no delegate is no call of a method.
    assert_eq!(
        diagnose("class C { void M() { int e = 0; e(); } }"),
        ["CS0149 'e': Method name expected"]
    );
}

// MARK: - obsolete

#[test]
fn a_use_of_something_obsolete_is_warned_about() {
    let declarations = "namespace System { public class ObsoleteAttribute : Attribute { public ObsoleteAttribute() { } public ObsoleteAttribute(string message) { } public ObsoleteAttribute(string message, bool error) { } } }";
    assert_eq!(
        diagnose(&format!(
            "{declarations} class C {{ [System.Obsolete] void Old() {{ }} void M() {{ Old(); }} }}"
        )),
        ["CS0612 'Old': 'C.Old()' is obsolete"]
    );
    assert_eq!(
        diagnose(&format!(
            "using System; {declarations} class C {{ [Obsolete(\"use New\")] public int Old; int M() => Old; }}"
        )),
        ["CS0618 'Old': 'C.Old' is obsolete: 'use New'"]
    );
    assert_eq!(
        codes(&format!(
            "using System; {declarations} class C {{ [Obsolete(\"gone\", true)] static void Old() {{ }} void M() {{ Old(); }} }}"
        )),
        ["CS0619"]
    );
    // Obsolete code may use obsolete code.
    assert_clean(&format!(
        "using System; {declarations} class C {{ [Obsolete] void Old() {{ }} [Obsolete] void Older() {{ Old(); }} }}"
    ));
}

// MARK: - cycles

#[test]
fn a_constant_defined_in_terms_of_itself_is_not_worked_out_forever() {
    // Folding `E.E` binds `F`'s initializer, which converts and folds `E`
    // again from scratch.
    diagnose(
        "class X : System.Attribute { public X(string s) { } } enum E { A, E = F, F = E } [X(E.E)] class C { }",
    );
}

#[test]
fn a_variance_that_expands_without_end_is_no_conversion() {
    diagnose(
        "interface IIn<in TIn> { } interface I : IIn<IIn<I>> { } delegate T D<out T>(); class C { static void Goo(D<IIn<I>> x) { } static void Goo(D<I> x) { } static void M() { Goo(null); } }",
    );
}

#[test]
fn a_default_value_that_calls_its_own_function_is_bound_once() {
    diagnose("class C { void M() { int L(int j = L()) => 0; L(); } }");
    diagnose("class C { void M() { int A(int i = B()) => 0; int B(int j = A()) => 0; A(); } }");
}

// MARK: - #pragma warning

#[test]
fn a_warning_switched_off_by_a_pragma_is_not_reported() {
    assert_clean(
        "class C { void M() {\n#pragma warning disable CS0168\n int x;\n#pragma warning restore CS0168\n } }",
    );
    assert_clean("class C { void M() {\n#pragma warning disable\n int x;\n } }");
    assert_eq!(
        codes(
            "class C { void M() {\n#pragma warning disable CS0168\n#pragma warning restore CS0168\n int x;\n } }"
        ),
        ["CS0168"]
    );
    assert_eq!(
        codes("class C { void M() {\n#pragma warning disable CS0219\n int x;\n } }"),
        ["CS0168"]
    );
    // An error is not a warning, whatever the pragma says.
    assert_eq!(
        codes("class C { void M() {\n#pragma warning disable\n int x = \"s\"; } }"),
        ["CS0029"]
    );
}

// MARK: - return

#[test]
fn a_return_that_does_not_fit_the_method_is_reported() {
    assert_eq!(
        diagnose("class C { void M() { return 1; } }"),
        [
            "CS0127 'return': Since 'C.M()' returns void, a return keyword must not be followed by an object expression"
        ]
    );
    assert_eq!(
        diagnose("class C { int M() { return; } }"),
        ["CS0126 'return': An object of a type convertible to 'int' is required"]
    );
    assert_clean("class C { void M() { return; } int N() { return 1; } }");
    assert_clean("using System; class C { void M() { Func<int> f = () => { return 1; }; f(); } }");
}

#[test]
fn a_method_without_a_body_must_say_why() {
    assert_eq!(
        diagnose("class C { void M(); }"),
        [
            "CS0501 'M': 'C.M()' must declare a body because it is not marked abstract, extern, or partial"
        ]
    );
    assert_eq!(
        diagnose("abstract class C { public abstract void M() { } }"),
        ["CS0500 'M': 'C.M()' cannot declare a body because it is marked abstract"]
    );
    assert_clean(
        "abstract class C { public abstract void M(); static extern void N(); partial void P(); interface I { void Q(); } }",
    );
}

#[test]
fn an_overload_that_may_be_named_is_not_blamed_on_one_that_may_not() {
    assert_clean(
        "class B { private void M(int x) { } public void M() { } } class D : B { void X(D d) { d.M(); } }",
    );
    assert_clean(
        "using System; class C { void Run() { } static void Run(int x) { } static void M() { Action<int> a = Run; a(1); } }",
    );
}

#[test]
fn a_local_function_called_with_the_wrong_arguments_says_why() {
    assert_eq!(
        codes(&with_flag("L(); static void L(int x) { }")),
        ["CS7036"]
    );
    assert_eq!(
        codes(&with_flag("L(1, 2); static void L(int x) { }")),
        ["CS1501"]
    );
    assert_eq!(
        codes(&with_flag("L(\"\"); static void L(int x) { }")),
        ["CS1503"]
    );
}

#[test]
fn a_labeled_break_or_continue_leaves_the_loop_it_names() {
    assert_clean(&with_flag(
        "outer: while (b) { for (int i = 0; i < n; i++) { if (b) continue outer; if (n > i) continue; break outer; } }",
    ));
    assert_clean(&with_flag(
        "s: switch (n) { case 1: while (b) { break s; } break; }",
    ));
    // Only the label written on the loop itself names it, and `continue`
    // never names a `switch`.
    assert_eq!(
        diagnose(&with_flag("a: b: while (b) { break a; }")),
        [
            "CS0164 'b': This label has not been referenced",
            "CS9393 'a': No enclosing loop or switch statement with the label 'a' out of which to break",
        ]
    );
    assert_eq!(
        codes(&with_flag("s: switch (n) { default: continue s; }")),
        ["CS9394"]
    );
    assert_eq!(codes(&with_flag("break;")), ["CS0139"]);
    // A lambda is a body of its own: nothing leaves the loop through it.
    assert_eq!(
        codes(&with_flag(
            "L: while (b) { Action a = () => { break L; }; }"
        )),
        ["CS0164", "CS9393"]
    );
}

#[test]
fn nothing_leaves_a_finally() {
    assert_eq!(
        codes(&with_flag("while (b) { try { } finally { break; } }")),
        ["CS0157"]
    );
    assert_eq!(codes(&with_flag("try { } finally { return; }")), ["CS0157"]);
    assert_clean(&with_flag("try { } finally { while (b) { break; } }"));
}

#[test]
fn a_for_step_after_a_body_that_never_ends_is_unreachable() {
    assert_eq!(
        codes(&with_flag("for (int i = 0; i < n; i++) { break; }")),
        ["CS0162"]
    );
    assert_clean(&with_flag(
        "for (int i = 0; i < n; i++) { if (b) continue; break; }",
    ));
}

#[test]
fn a_label_nothing_jumps_to_is_cs0164() {
    assert_eq!(codes(&with_flag("L: n++;")), ["CS0164"]);
    assert_clean(&with_flag("L: n++; if (b) goto L;"));
}

#[test]
fn a_modifier_the_declaration_cannot_have_is_cs0106() {
    assert_eq!(
        diagnose("class C { int P { scoped get; set; } async int F; }"),
        [
            "CS0106 'get': The modifier 'scoped' is not valid for this item",
            "CS0106 'F': The modifier 'async' is not valid for this item",
        ]
    );
    assert_eq!(
        codes("class C { readonly void M() { } } struct S { readonly void M() { } }"),
        ["CS0106"]
    );
    assert_eq!(
        codes("static class E { extension(object o) { public virtual void M() { } } }"),
        ["CS0106"]
    );
    assert_eq!(
        codes("unsafe struct S { public static fixed int x[10]; }"),
        ["CS0106"]
    );
    // `static` with what only an instance member can be is CS0112; an
    // interface's static members may be abstract.
    assert_eq!(
        diagnose("abstract class C { public static virtual void M() { } }"),
        ["CS0112 'M': A static member cannot be marked as 'virtual'"]
    );
    assert_clean("interface I { static abstract void M(); }");
    assert_clean(
        "struct S { public readonly int X; public int P { readonly get => 0; set { } } } \
         abstract class C { protected internal abstract int P { get; } public static extern void Q(); }",
    );
}

#[test]
fn partial_goes_last_and_only_where_it_means_something() {
    assert_eq!(codes("class C { int P { partial get; set; } }"), ["CS0267"]);
    assert_eq!(codes("partial public class C { }"), ["CS0267"]);
    assert_clean("public partial class C { partial void M(); }");
}

#[test]
fn a_local_copied_into_another_is_still_read() {
    assert_eq!(codes(&with_flag("int y; int x = y;")), ["CS0165"]);
    assert_clean(&with_flag("int y = 1; ref int x = ref y; x = 2;"));
    // `out int x` declares `x` unassigned until the call returns.
    assert_eq!(
        codes(
            "class C { static void M() { T(out int x, x); } static void T(out int a, int b) { a = b; } }"
        ),
        ["CS0165"]
    );
    // A lambda's body starts reachable, whatever is around it.
    assert_eq!(
        codes(
            "using System; class C { static void M() { return; Action f = () => { int y = y; }; } }"
        ),
        ["CS0162", "CS0165"]
    );
}

#[test]
fn a_call_to_a_local_function_reads_what_it_reads() {
    assert_eq!(
        diagnose(
            "class C { static void M() { int x; bool L2() => L1(); bool L1() => x == 0; L2(); } }"
        ),
        ["CS0165 'L2()': Use of unassigned local variable 'x'"]
    );
    assert_eq!(
        codes(
            "class C { static void M() { int x; bool L() => x == 0; System.Func<bool> f = L; x = 0; f(); } }"
        ),
        ["CS0165"]
    );
    assert_clean(
        "class C { static void M() { int x; void L() { x = 1; } L(); x++; int y = 0; int R() => y; R(); } }",
    );
}

#[test]
fn a_break_written_as_the_loop_body_leaves_the_loop() {
    assert_clean(&with_flag(
        "while (b) break; for (;;) break; L: while (b) continue L;",
    ));
    assert_eq!(
        codes(&with_flag("while (b) try { } finally { break; }")),
        ["CS0157"]
    );
}

#[test]
fn a_scoped_local_may_be_var_or_ref() {
    assert_clean(&with_flag(
        "int y = 1; scoped var r = 1; scoped ref int z = ref y; z = 3; r++;",
    ));
    assert_clean(
        "class C { static void M(out int x) { x = 1; } static void N() { M(out scoped var a); a++; \
         (scoped var b, var c) = (1, 2); b += c; foreach (scoped var d in new int[0]) { d.ToString(); } } }",
    );
}

#[test]
fn an_out_var_is_not_read_in_the_arguments_that_type_it() {
    assert_eq!(
        diagnose(
            "class C { static void M() { T(out var x, x); } static void T(out int a, object b) { a = 1; } }"
        ),
        [
            "CS8196 'x': Reference to an implicitly-typed variable 'x' is not permitted in this location."
        ]
    );
    assert_clean(
        "class C { static void M() { T(out int x, 1); T(out var y, 2); y++; x++; } static void T(out int a, object b) { a = 1; } }",
    );
}

/// Operators of interfaces whose bases go round in a circle, as they do in
/// code being edited: here files say different things about the same
/// interfaces, and together `I2 : I4` and `I4 : I2`. The search for the
/// operator of `-x` walked every path to its depth limit, millions of
/// lookups, and never came back (found by fuzzing, `examples/fuzz.rs` in
/// rustlyn-ide).
#[test]
fn an_operator_search_through_a_cycle_of_interfaces_comes_back() {
    let one = "\
public interface I1 { public static I1 operator -(I1 x) => x; }
public interface I2 : I1 { public static I2 operator -(I2 x) => x; }
public interface I3 : I2 { }
public interface I4 : I2, I1 { }
public interface I5 : I1, I2 { }
";
    let two = "\
public interface I3 { public static I3 operator -(I3 x) => x; }
public interface I4 : I1, I3 { public static I4 operator -(I4 x) => x; }
public interface I2 : I4 { }
class Test2 { static void Test<T>(T x) where T : Test2, I2 { var y = -x; var z = -(-x); } }
";
    let started = std::time::Instant::now();
    // The same file three times over, as a copied folder has it: every base
    // is written three times, and every level had six ways down.
    let compilation = Compilation::create(vec![
        parse(SourceText::new("One.cs", one)),
        parse(SourceText::new("Two.cs", two)),
        parse(SourceText::new("Two - Copy.cs", two)),
        parse(SourceText::new("Two - Copy (2).cs", two)),
    ]);
    let _ = compilation.semantic_diagnostics();
    assert!(
        started.elapsed().as_secs() < 5,
        "took {:?}",
        started.elapsed()
    );
}

/// Decimal literals with exponents of millions. The zeros an exponent stands
/// for were written out one at a time, at the front of the digits for a
/// negative one: `E-2859354M` never finished binding (found by fuzzing,
/// `examples/fuzz.rs` in rustlyn-ide).
#[test]
fn a_decimal_with_an_exponent_of_millions_is_bound_at_once() {
    let started = std::time::Instant::now();
    let _ = diagnose(
        "class C {
             decimal a = 79228162514264337593543950335E-2859354M;
             decimal b = 1E-2147483647M;
             decimal c = 0E2147483647M;
             decimal d = 1E2147483647M;
         }",
    );
    assert!(
        started.elapsed().as_secs() < 2,
        "took {:?}",
        started.elapsed()
    );
}

#[test]
fn a_local_of_a_lambda_in_a_field_initializer_sees_the_lambda_parameters() {
    // `static readonly Comparison<ItemData> ItemComparer = (a, b) => { var
    // favCompare = b.IsFavorite.CompareTo(a.IsFavorite); ... }`: the local's
    // initializer was bound again as if it were a field's of its own, where
    // `a` and `b` mean nothing.
    assert_eq!(
        codes(
            "class C { static readonly System.Func<int, int> F = a => { var x = a + 1; return x; }; }"
        ),
        Vec::<String>::new()
    );
    assert_eq!(
        codes("class C { System.Func<int, int> F = a => { var x = nope; return x; }; }"),
        ["CS0103"]
    );
}

/// Lambdas written inside one another, as generated code has them. Each
/// level is bound again for every binding of the ones around it, against
/// delegate types that are themselves as deep as what is left, so the work
/// grows with the cube of the depth: 300 levels took half a minute. This
/// bound is a generous one, there to catch it getting very much worse.
#[test]
fn lambdas_nested_a_hundred_and_fifty_deep_bind_in_bounded_time() {
    let source = format!(
        "class P {{ static void Main() {{ System.Func<object> f = {}1; }} }}",
        "() => ".repeat(150)
    );
    let started = std::time::Instant::now();
    let found = std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || codes(&source))
        .expect("a thread")
        .join()
        .expect("bound");
    assert!(found.is_empty(), "{found:?}");
    assert!(
        started.elapsed() < std::time::Duration::from_secs(60),
        "binding took {:?}",
        started.elapsed()
    );
}

#[test]
fn a_long_chain_of_additions_binds_in_time_proportional_to_it() {
    // Each `+` used to fold, test and copy the whole chain to its left: a
    // concatenation of 2000 terms, generated code or a buffer being typed
    // into, took the editor a minute. On the stack the editor gives a call.
    let chain = |operand: &str| {
        format!(
            "class C {{ string M(string a) {{ return {}\"b\"; }} }}",
            format!("{operand} + ").repeat(2000)
        )
    };
    let started = std::time::Instant::now();
    let found = std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || (codes(&chain("a")), codes(&chain("missing"))))
        .expect("a thread")
        .join()
        .expect("bound");
    assert!(found.0.is_empty(), "{:?}", found.0);
    assert_eq!(found.1.len(), 2000, "each `missing` is reported once");
    assert!(
        started.elapsed() < std::time::Duration::from_secs(20),
        "binding took {:?}",
        started.elapsed()
    );
}

#[test]
fn a_constant_cast_out_of_its_types_range_is_an_error_unless_unchecked() {
    // CS0221: constants are checked whatever `/checked` says.
    let found = diagnose(
        "enum E : byte { A }
class C {
    void M() {
        int a = (int)2147483648L;
        byte b = (byte)300;
        uint c = (uint)(-1);
        int d = (int)1e10;
        E e = (E)256;
        char f = (char)(-1);
    }
}",
    );
    assert_eq!(
        found,
        [
            "CS0221 '(int)2147483648L': Constant value '2147483648' cannot be converted to a 'int' (use 'unchecked' syntax to override)",
            "CS0221 '(byte)300': Constant value '300' cannot be converted to a 'byte' (use 'unchecked' syntax to override)",
            "CS0221 '(uint)(-1)': Constant value '-1' cannot be converted to a 'uint' (use 'unchecked' syntax to override)",
            "CS0221 '(int)1e10': Constant value '10000000000' cannot be converted to a 'int' (use 'unchecked' syntax to override)",
            "CS0221 '(E)256': Constant value '256' cannot be converted to a 'E' (use 'unchecked' syntax to override)",
            "CS0221 '(char)(-1)': Constant value '-1' cannot be converted to a 'char' (use 'unchecked' syntax to override)",
        ]
    );
    // What fits, what is truncated into range, and what is said to wrap.
    assert!(
        codes(
            "class C {
    void M() {
        int a = unchecked((int)2147483648L);
        byte b = (byte)255;
        int c = (int)1.9;
        long d = (long)2147483647;
        unchecked { int e = (int)4294967295u; }
        int f = checked(unchecked((int)4294967295u));
        sbyte g = (sbyte)-128;
        uint h = (uint)2147483648L;
    }
}"
        )
        .is_empty()
    );
}

#[test]
fn an_extern_local_function_has_no_out_parameters_to_assign() {
    // Its body is not C#, as Roslyn's own `ShadowCopyAnalyzerPathResolver`
    // declares one: `static extern bool Get(out int value);` inside a method.
    let found = codes(
        "class C {
    static int M() {
        return Get(out var value) ? value : 0;
        static extern bool Get(out int value);
    }
}",
    );
    assert!(!found.iter().any(|code| code == "CS0177"), "{found:?}");
}

#[test]
fn a_nested_type_named_through_a_constructed_base_is_that_constructions() {
    // `E.A` in a class deriving from `B<int>` is a `B<int>.E`, as an `E`
    // declared there is (Roslyn's CSharpLineDirectiveMap and PositionState).
    let found = codes(
        "class B<T> { public enum E { A } public struct S { public E State; } }
class D : B<int> {
    void M(S s) {
        E e = E.A;
        E f = s.State;
        bool g = s.State == E.A;
    }
}",
    );
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn an_array_of_nullable_arrays_is_created_with_an_initializer() {
    // `new object[,]?[] { … }` was `new object[,]` and a conditional `?[`.
    let found = codes(
        "#nullable enable
class C { void M() {
    var a = new object[,]?[] { null, new object[,] { { 1 } } };
    var b = new object[3]?[0];
} }",
    );
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn a_lambda_states_a_nullable_return_type() {
    // `string? () => null` (Roslyn's LambdaTests.LambdaReturnType_07); a
    // `?` after a name that could be a condition stays a conditional.
    let found = codes(
        "#nullable enable
class C { void M(bool flag) {
    System.Delegate a = string? () => default;
    System.Func<int?> b = int? () => null;
    System.Func<int, int> c = flag ? (int x) => x : (int y) => y;
} }",
    );
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn a_coalesce_converted_by_an_operator_assigns_in_its_conditional_access() {
    // `c?.M2(x = 0) ?? …` with the left converted by a user-defined
    // operator: where the left is not null the call ran (Roslyn's
    // FlowTests.NullCoalescing_CondAccess_UserDefinedConv_01).
    let found = codes(
        "struct S { }
struct C
{
    public static implicit operator S(C? c) => default(S);
    void M1(C? c1)
    {
        int x;
        S s = c1?.M2(x = 0) ?? c1.Value.M3(x = 0);
        x.ToString();
    }
    C M2(object obj) => this;
    S M3(object obj) => this;
}",
    );
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn a_deconstruction_names_the_elements_of_its_value() {
    // `var u = ((x, y) = t);` holds a `(x, y)` (Roslyn's
    // NullableReferenceTypesTests.Deconstruction_21).
    let found = codes(
        "class Program
{
    static void F<T, U>((T, U) t) where U : struct
    {
        object x;
        object y;
        var u = ((x, y) = t);
        u.x.ToString();
        u.y.ToString();
    }
}",
    );
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn a_top_level_local_function_may_have_attributes() {
    // `[DoesNotReturn] static void Fail()` at the top of a file is a local
    // function of the program, as it is without the attribute (Roslyn's
    // NullableReferenceTypesTests.EnforcedInLambdaBody_DoesNotReturn).
    let found = codes("var f = static () => g();\n[System.Obsolete] static int g() => 1;\n");
    assert!(!found.iter().any(|code| code == "CS0103"), "{found:?}");
}

#[test]
fn a_lambda_states_a_tuple_return_type() {
    // `(int, int) () => default` (Roslyn's LambdaTests.LambdaReturnType_06).
    let found =
        codes("class C { void M() { System.Func<(int X, int Y)> e = (int, int) () => default; } }");
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn a_lambda_returning_null_first_infers_from_its_other_returns() {
    // `if (b) return null; else return new object();` gives `T` = `object`
    // (Roslyn's NullableReferenceTypesTests.ReturningValues_WithoutType).
    let found = codes(
        "class Program
{
    static void M<T>(System.Func<T> t) { }
    static void F(bool b)
    {
        M(() => { if (b) return null; else return new object(); });
        M(() => { if (b) return new object(); else return null; });
    }
}",
    );
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn a_type_parameter_converts_by_its_base_classs_operators() {
    // `if (instance)` on a `T : UnityEngine.Object`: the user-defined
    // conversions of a type parameter are its effective base class's
    // (§10.5.3), here `Object`'s `implicit operator bool`.
    let found = codes(
        "class Object { public static implicit operator bool(Object o) => o != null; }
class Settings<T> where T : Object
{
    static T s_instance;
    static bool HasInstance => s_instance;
    void M() { if (s_instance) { } if (!s_instance) { } }
}",
    );
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn an_extension_method_is_called_where_no_instance_method_applies() {
    // `vertices.ToString(\",\")` where the type's own `ToString()` takes no
    // argument: with no applicable instance method the call goes on to the
    // extension methods (§12.8.10.3).
    let found = codes(
        "static class Text { public static string ToString<T>(this T[] items, string separator) => separator; }
class Ring
{
    int[] vertices;
    string M() => vertices.ToString(\",\");
}",
    );
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn a_struct_constrained_extension_is_called_on_its_receiver() {
    // Morpeh's `entity.SetComponent(new Timer())` and `entity.Has<Timer>()`:
    // the type parameter's constraints (`struct`, an interface) are no
    // operators to look for.
    let found = codes(
        "public struct Entity { }
public interface IDataComponent { }
public struct Timer : IDataComponent { }
public static class EntityExtensions
{
    public static void SetComponent<T>(this Entity entity, T value) where T : struct, IDataComponent { }
    public static bool Has<T>(this Entity entity) where T : struct, IDataComponent => true;
}
class C { bool M(Entity entity) { entity.SetComponent(new Timer()); return entity.Has<Timer>(); } }",
    );
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn null_reaches_a_type_through_its_operator_from_a_class() {
    // ShaderGraph's `m_OutputNode = null` on a `JsonRef<T>` with `implicit
    // operator JsonRef<T>(T value)`: `null` converts to the class `T`, and
    // the operator takes it the rest of the way (§10.5.4).
    let found = codes(
        "class JsonObject { }
abstract class Node : JsonObject { }
struct JsonRef<T> where T : JsonObject
{
    T m_Value;
    public static implicit operator T(JsonRef<T> jsonRef) => jsonRef.m_Value;
    public static implicit operator JsonRef<T>(T value) => new JsonRef<T> { m_Value = value };
}
class Graph { JsonRef<Node> m_OutputNode; void M() { m_OutputNode = null; } }",
    );
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn a_derived_generic_type_converts_by_its_base_classs_operator() {
    // ProBuilder's `if (pref)` on a `Pref<bool> : UserSetting<bool>`, whose
    // base declares `implicit operator T(UserSetting<T>)`: the operators of
    // the source's base classes are candidates too (§10.5.3), with the base
    // as the derived type constructs it.
    let found = codes(
        "class UserSetting<T> { T value; public static implicit operator T(UserSetting<T> pref) => pref.value; }
class Pref<T> : UserSetting<T> { }
class Guides { static Pref<bool> s_Origin; void M() { if (s_Origin) { } bool b = s_Origin; } }",
    );
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn an_override_calls_its_base_with_its_own_type_parameter() {
    // `protected override TResult Build<TResult>(…) => base.Build<TResult>(…)`:
    // the override's `TResult` is the one the base call is constructed with.
    let found = codes(
        "class Builder { protected virtual TResult Build<TResult>(int input) where TResult : class => null; }
class Caching : Builder { protected override TResult Build<TResult>(int input) { return base.Build<TResult>(input); } }",
    );
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn an_extension_receiver_takes_no_user_defined_conversion() {
    // UniTask's `GetAwaiter(this AsyncOperationHandle)` beside
    // `GetAwaiter<T>(this AsyncOperationHandle<T>)`: an
    // `AsyncOperationHandle<T>` reaches the first only through its implicit
    // operator, which a receiver may not use (§12.8.10.3), so `await` gives
    // the `T`.
    let found = codes(
        "struct Handle { }
struct Handle<T> { public static implicit operator Handle(Handle<T> h) => default; }
struct Awaiter { public void GetResult() { } }
struct Awaiter<T> { public T GetResult() => default; }
static class Extensions
{
    public static Awaiter GetAwaiter(this Handle handle) => default;
    public static Awaiter<T> GetAwaiter<T>(this Handle<T> handle) => default;
}
class Loader
{
    static Handle<T> Load<T>() => default;
    string M() { string s = Load<string>().GetAwaiter().GetResult(); return s; }
}",
    );
    assert!(found.is_empty(), "{found:?}");
    // Nor is the operator a way in where it is the only candidate.
    let found = codes(
        "struct Handle { }
struct Handle<T> { public static implicit operator Handle(Handle<T> h) => default; }
static class Extensions { public static int Twice(this Handle handle) => 2; }
class C { int M(Handle<int> h) => h.Twice(); }",
    );
    assert_eq!(found, ["CS1061"]);
}

#[test]
fn an_alias_target_is_read_where_the_alias_is_declared() {
    // Hot Reload's `using Task = System.Threading.Tasks.Task;` at the top of
    // a file whose code is in `namespace SingularityGroup.HotReload.Editor`,
    // with a `SingularityGroup.HotReload.System` namespace elsewhere: the
    // alias names what `System` is where the alias is written (§14.5.2).
    let found = codes(
        "using Task = System.Threading.Tasks.Task;
namespace System.Threading.Tasks { public class Task { public static Task Delay(int ms) => null; } }
namespace HotReload.System { class Other { } }
namespace HotReload.Editor { class Tab { Task M() => Task.Delay(1); } }",
    );
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn a_field_initializer_converts_only_where_an_assignment_would() {
    // A field's or property's initializer assigns to it: `int count =
    // "many";` is CS0029 there as it is for a local. What an assignment
    // takes, the initializer takes.
    let found = codes(
        "using System;
using System.Collections.Generic;
class C
{
    int count = \"many\", other = 1;
    string Name { get; } = 3;
    byte small = 1;
    object nothing = null;
    Func<int, int> twice = x => x * 2;
    Action run = Run;
    List<int> list = new();
    int[] numbers = { 1, 2 };
    int[] more = [3, 4];
    long wide = 1 > 0 ? 2 : 3;
    int picked = 1 switch { 1 => 2, _ => 3 };
    double scale = default;
    static void Run() { }
}",
    );
    assert_eq!(found, ["CS0029", "CS0029"], "{found:?}");
}

#[test]
fn a_using_twice_an_outer_type_parameter_and_an_async_that_never_waits_are_warned_about() {
    // CS0105, CS0693 and CS1998 as Roslyn reports them, at the second
    // `using`'s name, the inner type parameter and the method's name or the
    // lambda's arrow. Only an `await` of the function's own counts, and an
    // `async` iterator is not one that would.
    // The core library these are compiled against has no `Task`: only the
    // warnings are looked at.
    let found: Vec<String> = diagnose(
        "using System;
using System.Threading.Tasks;
using System;
using static System.Math;
using global::System.Threading.Tasks;
class Outer<T>
{
    public U Plain<U>() => default;
    public T Get<T>() => default;
    class Inner<T> { }
    async Task Waits() { await Task.Yield(); }
    async Task Never() { }
    async Task NestedOnly() { Func<Task> f = async () => await Task.Yield(); }
    void Lambdas() { Func<Task> f = async () => { }; Func<Task> g = async () => await Task.Yield(); }
}",
    )
    .into_iter()
    .filter(|line| ["CS0105", "CS0693", "CS1998"].contains(&&line[..6]))
    .collect();
    assert_eq!(
        found,
        [
            "CS0105 'System': The using directive for 'System' appeared previously in this namespace",
            "CS0105 'global::System.Threading.Tasks': The using directive for 'System.Threading.Tasks' appeared previously in this namespace",
            "CS0693 'T': Type parameter 'T' has the same name as the type parameter from outer type 'Outer<T>'",
            "CS0693 'T': Type parameter 'T' has the same name as the type parameter from outer type 'Outer<T>'",
            "CS1998 'Never': This async method lacks 'await' operators and will run synchronously. Consider using the 'await' operator to await non-blocking API calls, or 'await Task.Run(...)' to do CPU-bound work on a background thread.",
            "CS1998 'NestedOnly': This async method lacks 'await' operators and will run synchronously. Consider using the 'await' operator to await non-blocking API calls, or 'await Task.Run(...)' to do CPU-bound work on a background thread.",
            "CS1998 '=>': This async method lacks 'await' operators and will run synchronously. Consider using the 'await' operator to await non-blocking API calls, or 'await Task.Run(...)' to do CPU-bound work on a background thread.",
        ],
        "{found:#?}"
    );
}

#[test]
fn an_unused_catch_variable_beside_another_of_its_name_is_warned_about() {
    // Two `catch (... e)` in one method: each `e` is its clause's, and the
    // one never read is CS0168 as it would be alone.
    let found = codes(&in_method(
        "try { } catch (ArgumentException e) { } try { } catch (Exception e) { Console.WriteLine(e); }",
    ));
    assert_eq!(found, ["CS0168"], "{found:?}");
}

#[test]
fn a_field_hides_an_inherited_method_of_its_name() {
    // `public Action Close` in a class whose generic base has `Close()`:
    // CS0108 against the base as the class constructs it.
    let found = diagnose(
        "using System;
class UiComponent<T> { public void Close() { } public int Count; }
class Panel : UiComponent<Panel> { public Action Close = null; public void Count() { } }",
    );
    assert_eq!(
        found,
        [
            "CS0108 'Close': 'Panel.Close' hides inherited member 'UiComponent<Panel>.Close()'. Use the new keyword if hiding was intended.",
            "CS0108 'Count': 'Panel.Count()' hides inherited member 'UiComponent<Panel>.Count'. Use the new keyword if hiding was intended.",
        ],
        "{found:#?}"
    );
}

#[test]
fn await_of_something_with_no_awaiter_is_an_error() {
    // `await` of a value with no `GetAwaiter` compiled and failed to emit:
    // it is CS1061, and of a `void` call CS4008.
    let found = diagnose(
        "class C
{
    static void Nothing() { }
    async void M() { await 5; await Nothing(); }
}",
    );
    assert_eq!(
        found,
        [
            "CS1061 'await 5': 'int' does not contain a definition for 'GetAwaiter' and no accessible extension method 'GetAwaiter' accepting a first argument of type 'int' could be found (are you missing a using directive or an assembly reference?)",
            "CS4008 'await Nothing()': Cannot await 'void'",
        ],
        "{found:#?}"
    );
}

#[test]
fn a_nullable_annotation_outside_its_context_is_warned_about() {
    // CS8632 at the `?` of a reference type or a type parameter that may be
    // one, where annotations are off; a value type's `?` is `Nullable<T>`,
    // and `#nullable enable` turns them on until `restore`.
    let found: Vec<String> = diagnose(
        "class C<T, S> where S : struct
{
    string? name;
    int? count;
    T? some;
    S? value;
    C<T, S>? next;
#nullable enable
    string? kept;
#nullable restore
    object? again;
}",
    )
    .into_iter()
    .filter(|line| line.starts_with("CS8632"))
    .collect();
    let warning = "The annotation for nullable reference types should only be used in code within a '#nullable' annotations context.";
    assert_eq!(
        found,
        [
            format!("CS8632 '?': {warning}"),
            format!("CS8632 '?': {warning}"),
            format!("CS8632 '?': {warning}"),
            format!("CS8632 '?': {warning}"),
        ],
        "{found:#?}"
    );
}

#[test]
fn a_switch_expression_that_leaves_a_value_out_is_warned_about() {
    // CS8509 where a named member or a value is not covered, CS8524 where
    // only unnamed enum values are; at the `switch` keyword, once even in a
    // lambda bound more than once. `_`, `var` and arms not judged (types,
    // relations) keep it quiet; an arm with `when` covers nothing.
    let found: Vec<String> = diagnose(
        "using System;
enum Kind { A, B, C }
class C
{
    int Missing(Kind k) => k switch { Kind.A => 1, Kind.B => 2 };
    int Named(Kind k) => k switch { Kind.A or Kind.B => 1, Kind.C => 2 };
    int Discard(Kind k) => k switch { Kind.A => 1, _ => 2 };
    int Guarded(Kind k, bool b) => k switch { Kind.A => 1, Kind.B => 2, _ when b => 3 };
    int Numbers(int n) => n switch { 0 => 1, 1 => 2, 2 => 3, 3 => 4 };
    int Var(int n) => n switch { 0 => 1, var other => other };
    int Relational(int n) => n switch { < 0 => -1, >= 0 => 1 };
    int Flag(bool b) => b switch { true => 1, false => 0 };
    int Half(bool b) => b switch { true => 1 };
    int Typed(object o) => o switch { string => 1, int => 2 };
    int Nullable(Kind? k) => k switch { Kind.A => 1 };
    Func<Kind, int> Lambda() => k => k switch { Kind.A => 1 };
}",
    )
    .into_iter()
    .filter(|line| line.starts_with("CS8509") || line.starts_with("CS8524"))
    .collect();
    let missing = |example: &str| {
        format!(
            "CS8509 'switch': The switch expression does not handle all possible values of its input type (it is not exhaustive). For example, the pattern '{example}' is not covered."
        )
    };
    assert_eq!(
        found,
        [
            missing("Kind.C"),
            "CS8524 'switch': The switch expression does not handle some values of its input type (it is not exhaustive) involving an unnamed enum value. For example, the pattern '(Kind)3' is not covered.".to_string(),
            missing("Kind.C"),
            missing("4"),
            missing("false"),
            missing("Kind.B"),
        ],
        "{found:#?}"
    );
}

#[test]
fn equality_without_its_overrides_is_warned_about() {
    // CS0660 and CS0661 at a type with `==` but no `Equals` or `GetHashCode`
    // override, CS0659 at one overriding `Equals` alone; a record makes them
    // itself, and a type with all three is fine.
    let found: Vec<String> = diagnose(
        "struct Pair<T>
{
    public static bool operator ==(Pair<T> a, Pair<T> b) => true;
    public static bool operator !=(Pair<T> a, Pair<T> b) => false;
}
class Key
{
    public override bool Equals(object o) => true;
}
class Whole
{
    public static bool operator ==(Whole a, Whole b) => true;
    public static bool operator !=(Whole a, Whole b) => false;
    public override bool Equals(object o) => true;
    public override int GetHashCode() => 0;
}
record Point(int X);",
    )
    .into_iter()
    .filter(|line| line.starts_with("CS06"))
    .collect();
    assert_eq!(
        found,
        [
            "CS0660 'Pair': 'Pair<T>' defines operator == or operator != but does not override Object.Equals(object o)",
            "CS0661 'Pair': 'Pair<T>' defines operator == or operator != but does not override Object.GetHashCode()",
            "CS0659 'Key': 'Key' overrides Object.Equals(object o) but does not override Object.GetHashCode()",
        ],
        "{found:#?}"
    );
}

#[test]
fn an_obsolete_override_of_a_member_that_is_not_is_warned_about() {
    // CS0809 at the override's name; one of an obsolete member is fine.
    let found: Vec<String> = diagnose(
        "using System;
class Base
{
    public virtual bool IsEmpty() => true;
    [Obsolete] public virtual void Old() { }
}
class Derived : Base
{
    [Obsolete] public override bool IsEmpty() => false;
    [Obsolete] public override void Old() { }
}",
    )
    .into_iter()
    .filter(|line| line.starts_with("CS0809"))
    .collect();
    assert_eq!(
        found,
        [
            "CS0809 'IsEmpty': Obsolete member 'Derived.IsEmpty()' overrides non-obsolete member 'Base.IsEmpty()'"
        ],
        "{found:#?}"
    );
}

// MARK: - constants that have no value

/// The errors among `wanted` that a file gets, whatever else it is told —
/// that a local is never read, mostly.
fn only(source: &str, wanted: &[&str]) -> Vec<String> {
    codes(source)
        .into_iter()
        .filter(|code| wanted.contains(&code.as_str()))
        .collect()
}

#[test]
fn a_constant_that_overflows_its_type_is_cs0220() {
    // Worked out by the compiler, so an error wherever it is written — it
    // was folded to the wrapped value without a word.
    assert_eq!(
        diagnose("class C { const int Over = 2147483647 + 1; }"),
        ["CS0220 '2147483647 + 1': The operation overflows at compile time in checked mode"]
    );
    for body in [
        "int i = 2147483647 + 1;",
        "long l = 9223372036854775807 * 2;",
        "uint u = 0u - 1;",
        "ulong u = 0xFFFFFFFFFFFFFFFF + 1;",
        "int i = -(-2147483648);",
        "long l = -(-9223372036854775808);",
        "int i = (-2147483647 - 1) / -1;",
        "const int K = 2147483647 + 1;",
        "int i = 'a' * 100000000;",
        "int i = checked(2147483647 + 1);",
        // Only the part that overflowed: what is worked out from it has no
        // value to overflow again.
        "int i = 2147483647 + 1 - 1;",
        "int i = (2147483647 + 1) + n;",
        "int i = 2147483647 * 2 + n;",
    ] {
        assert_eq!(codes(&with_flag(body)), ["CS0220"], "{body}");
    }
    assert_eq!(
        codes("enum E { A = 1 } class C { const E Over = E.A + 2147483647; }"),
        ["CS0220"]
    );
}

#[test]
fn arithmetic_that_stays_in_range_or_is_unchecked_is_not_cs0220() {
    for body in [
        "int i = unchecked(2147483647 + 1);",
        "unchecked { int i = 2147483647 + 1; int j = -(-2147483648); const int K = 2147483647 * 2; }",
        "int hash = unchecked((int)2166136261 * 16777619);",
        // Not constants: what they come to is found when they run.
        "int i = n + 2147483647;",
        "int i = n + 2147483647 + 1;",
        "checked { int i = n + 2147483647; }",
        // A shift never overflows: the bits fall off.
        "int i = 1 << 40; int j = 1 << 31; uint k = 1u << 31;",
        // In range, at the edges.
        "int i = 2147483647 - 1 + 1; int j = -2147483648 + 0; long l = 2147483647 + 1L;",
        "ulong u = 0xFFFFFFFFFFFFFFFF - 1; uint v = 0xFFFFFFFF + 0u; long m = -9223372036854775808;",
        "int r = (-2147483647 - 1) % -1;",
        // Floating point has infinities, not overflows.
        "double d = 1e308 * 10; float f = 3e38f * 10;",
        "string s = \"a\" + \"b\" + 1;",
    ] {
        let found = only(&with_flag(body), &["CS0220", "CS0020", "CS0221"]);
        assert!(found.is_empty(), "{body}: {found:?}");
    }
    assert_clean(
        "[System.Flags] enum Bits : ulong { None, Top = 1UL << 63, All = 0xFFFFFFFFFFFFFFFF, Rest = All - Top }
         class C { const int Size = sizeof(int) * Count; const int Count = 4; }",
    );
}

#[test]
fn a_constant_divided_by_a_constant_zero_is_cs0020() {
    assert_eq!(
        diagnose("class C { const int Zero = 5 / 0; }"),
        ["CS0020 '5 / 0': Division by constant zero"]
    );
    assert_eq!(codes(&with_flag("int i = 5 % 0;")), ["CS0020"]);
    assert_eq!(codes(&with_flag("long l = 5L / (1 - 1);")), ["CS0020"]);
    // A variable divided by zero throws when it runs, and floating point
    // has an answer.
    let found = only(
        &with_flag("int i = n / 0; int j = n % 0; double d = 1.0 / 0; double e = n / 0.0;"),
        &["CS0020", "CS0220"],
    );
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn a_constant_defined_in_terms_of_itself_is_cs0110() {
    assert_eq!(
        diagnose("class C { const int A = B + 1; const int B = A + 1; const int Fine = 1; }"),
        [
            "CS0110 'A': The evaluation of the constant value for 'C.A' involves a circular definition"
        ]
    );
    assert_eq!(
        diagnose("class C { const int Self = Self; }"),
        [
            "CS0110 'Self': The evaluation of the constant value for 'C.Self' involves a circular definition"
        ]
    );
    assert_eq!(
        diagnose("enum Loop { P = Q, Q = P, R = 1 }"),
        [
            "CS0110 'P': The evaluation of the constant value for 'Loop.P' involves a circular definition"
        ]
    );
    // Through a third, and across two types: once, where it is first written.
    assert_eq!(
        codes(
            "class A { public const int X = B.Y; } class B { public const int Y = C.Z; } class C { public const int Z = A.X; }"
        ),
        ["CS0110"]
    );
}

#[test]
fn a_constant_that_names_itself_without_needing_its_value_is_not_cs0110() {
    assert_clean(
        "class C {
            public const string Name = nameof(Name);
            public const string Both = nameof(Both) + nameof(Name);
            public const int Size = sizeof(int) * Count;
            public const int Count = 4;
            public const int Next = Count + 1;
            static int Default(int x = Count, string s = Name) => x;
        }
        enum Flags { All = A | B, A = 1, B = 2, C, D = C * 2 }
        enum Order { A, B = A + C, C = 1 }",
    );
}

// MARK: - definite assignment across a goto

/// A method body of a class with `Use(int)` and `Cond()` to call.
fn jumping(body: &str) -> String {
    format!(
        "class C {{ static void Use(int x) {{ }} static bool Cond() => true; void M() {{ {body} }} }}"
    )
}

#[test]
fn a_local_a_goto_reaches_unassigned_is_cs0165() {
    // A body with a `goto` used to get no CS0165 at all: the jump is one
    // the walk could not follow, so it said nothing — about any local in
    // the method.
    assert_eq!(
        diagnose(&jumping("int x; goto L; L: Use(x);")),
        ["CS0165 'x': Use of unassigned local variable 'x'"]
    );
    for body in [
        // Over the assignment, and over the declaration that makes it.
        "int x; if (Cond()) goto L; x = 2; L: Use(x);",
        "int x; for (int i = 0; i < 3; i++) { if (i == 1) goto Done; } x = 1; Done: Use(x);",
        "int x; { goto L; } L: { Use(x); }",
        // Back to a label walked before the jump was seen.
        "int x; goto B; A: Use(x); return; B: if (Cond()) x = 1; goto A;",
        "int x; int n = 0; L: if (n > 0) Use(x); x = 1; n++; if (n < 3) goto L;",
        // The one of two that a path leaves out.
        "int x; int y; A: if (Cond()) { x = 1; goto B; } y = 2; goto A; B: Use(x); Use(y);",
        // In a lambda and in a local function, which jump within themselves.
        "System.Func<int> f = () => { int y; if (Cond()) goto L; y = 1; L: return y; }; Use(f());",
        "void Local() { int z; goto Q; Q: Use(z); } Local();",
        // `goto case` too.
        "int x; switch (Cond() ? 1 : 2) { case 1: goto case 2; case 2: Use(x); break; }",
        // Round again through a declaration: unassigned the first time.
        "int n = 0; L: int x; if (n > 0) Use(x); x = 1; n++; if (n < 3) goto L;",
        "for (int i = 0; i < 3; i++) { int x; if (i > 0) Use(x); x = i; if (i == 2) goto End; } End: ;",
        "int k = 0; Top: { int y; if (k > 0) Use(y); y = 1; } k++; if (k < 2) goto Top;",
        "goto Mid; Back: int v; Use(v); return; Mid: if (Cond()) v = 1; goto Back;",
    ] {
        assert_eq!(only(&jumping(body), &["CS0165"]), ["CS0165"], "{body}");
    }
    // A jump over the declaration itself reads what nothing assigned.
    assert_eq!(
        only(&jumping("goto L; int x = 1; L: Use(x);"), &["CS0165"]),
        ["CS0165"]
    );
    // And an `out` parameter a jump leaves unassigned on the way out.
    assert_eq!(
        codes("class C { void M(out int r) { goto L; L: return; } }"),
        ["CS0177"]
    );
}

#[test]
fn a_local_assigned_on_every_way_to_a_label_is_not_cs0165() {
    for body in [
        "int x; if (Cond()) { x = 1; goto L; } x = 2; L: Use(x);",
        "int x; goto B; A: Use(x); return; B: x = 1; goto A;",
        "int x = 0; int n = 0; L: Use(x); n++; if (n < 3) goto L;",
        "int x; int n = 0; L: x = n; n++; if (n < 3) goto L; Use(x);",
        "int x; while (true) { if (Cond()) { x = 1; goto Out; } } Out: Use(x);",
        "int x; try { if (Cond()) goto L; x = 1; } catch { x = 2; } Use(x); return; L: x = 3; Use(x);",
        "int x; switch (Cond() ? 1 : 2) { case 1: x = 1; goto case 2; case 2: x = 2; break; default: x = 3; break; } Use(x);",
        "int x; goto L2; L1: Use(x); goto L3; L2: x = 1; goto L1; L3: return;",
        "int a; L: if (Cond()) { a = 1; } else goto L; Use(a);",
        "int x; if (Cond()) { x = 1; } else { goto Skip; } Use(x); Skip: ;",
        "int x; do { if (Cond()) goto End; x = 1; Use(x); } while (Cond()); End: ;",
    ] {
        let found = only(&jumping(body), &["CS0165", "CS0177", "CS0269"]);
        assert!(found.is_empty(), "{body}: {found:?}");
    }
    assert_clean(
        "class C { static bool Cond() => true; void M(out int r) { if (Cond()) goto L; r = 1; return; L: r = 2; } }",
    );
    // A bare `int x;` assigns nothing and takes nothing away (§9.4.4.7):
    // a jump back to before it, with `x` assigned on the way, reads it
    // after — which the framework's vectorised loops are written as.
    let found = only(
        &jumping("goto Start; Found: int x; Use(x); return; Start: x = 1; goto Found;"),
        &["CS0165"],
    );
    assert!(found.is_empty(), "{found:?}");
}

// MARK: - casts nothing can make

/// Types to cast between, and a method whose parameters are one of each.
fn casting(body: &str) -> String {
    format!(
        "enum E {{ A }} enum F {{ B }} struct S {{ }} struct Other {{ }}
         struct WithOp {{ public static explicit operator long(WithOp w) => 1; public static implicit operator WithOp(string s) => default; }}
         class A {{ }} class B : A {{ }} class C {{ }} sealed class Sealed {{ }}
         class Conv {{ public static explicit operator Conv(int x) => null; }} class DerivedConv : Conv {{ }}
         interface I {{ }} class Impl : I {{ }} class G<T> {{ }} delegate void D1(); delegate void D2();
         class Tests<T, U> where T : class {{
             void M(int i, long l, string s, bool b, char c, double d, object o, E e, F f, S st, A a, B bb, C cc, Sealed se,
                    I it, Impl im, int? ni, bool? nb, WithOp w, Conv cv, DerivedConv dc, G<int> gi, G<long> gl, T t, U u,
                    int[] ia, object[] oa, string[] sa, D1 d1) {{ {body} }}
         }}"
    )
}

#[test]
fn a_cast_between_types_nothing_converts_is_cs0030() {
    // `(string)5` was bound as a boxing and `(int)"x"` as an unboxing, by
    // the shapes of the two types, and both compiled.
    assert_eq!(
        diagnose(&casting("var x = (string)i;")),
        ["CS0030 '(string)i': Cannot convert type 'int' to 'string'"]
    );
    assert_eq!(
        diagnose(&casting("var x = (int)s;")),
        ["CS0030 '(int)s': Cannot convert type 'string' to 'int'"]
    );
    for cast in [
        // A `bool` is no number, and a `string` no character.
        "(bool)i",
        "(int)b",
        "(double)b",
        "(string)b",
        "(char)s",
        "(string)c",
        "(E)b",
        "(bool)e",
        "(E)s",
        "(string)e",
        // A struct reaches no class but `object`, and no other struct.
        "(S)i",
        "(int)st",
        "(Other)st",
        "(S)a",
        "(A)st",
        "(string)st",
        // Two classes neither of which derives from the other.
        "(C)a",
        "(A)cc",
        "(Sealed)a",
        "(string)a",
        "(A)s",
        "(G<long>)gi",
        // A nullable converts as what it holds.
        "(int)nb",
        "(bool?)i",
        // An operator that has nothing to say about these two.
        "(S)w",
        "(C)cv",
        "(bool)w",
    ] {
        assert_eq!(
            only(&casting(&format!("var x = {cast};")), &["CS0030"]),
            ["CS0030"],
            "{cast}"
        );
    }
}

#[test]
fn a_cast_the_language_has_is_not_cs0030() {
    for cast in [
        // Numbers, characters and enums among themselves.
        "(long)i",
        "(int)l",
        "(E)i",
        "(int)e",
        "(F)e",
        "(char)i",
        "(int)c",
        "(byte)e",
        "(double)i",
        "(int)d",
        "(E)0",
        // Up, down and across a hierarchy that is one.
        "(B)a",
        "(A)bb",
        "(object)i",
        "(int)o",
        "(string)o",
        "(object)s",
        "(A)o",
        // An interface may be implemented by what derives from the class.
        "(I)a",
        "(A)it",
        "(I)im",
        "(Impl)it",
        "(I)o",
        // Nullables.
        "(int?)i",
        "(int)ni",
        "(long?)ni",
        "(E?)i",
        // Operators, with a standard conversion before or after.
        "(long)w",
        "(int)w",
        "(WithOp)s",
        "(Conv)i",
        "(Conv)d",
        "(DerivedConv)cv",
        "(Conv)dc",
        // Type parameters, arrays and delegates have rules of their own.
        "(T)o",
        "(T)(object)u",
        "(U)(object)i",
        "(A)(object)t",
        "(I)t",
        "(T)it",
        "(object[])sa",
        "(string[])oa",
        "(int[])o",
        "(object)ia",
        "(D2)(object)d1",
        "(D1)null",
        "(string)null",
        "(A)null",
        "(int?)null",
    ] {
        let found = only(&casting(&format!("var x = {cast};")), &["CS0030"]);
        assert!(found.is_empty(), "{cast}: {found:?}");
    }
}

// MARK: - calls that could mean two methods

/// Overloads to call, and a method whose parameters are the arguments.
fn overloaded(body: &str) -> String {
    format!(
        "interface IA {{ }} interface IB {{ }} class AB : IA, IB {{ }}
         class Animal {{ }} class Dog : Animal {{ }} class Puppy : Dog {{ }}
         class C {{
             static void M(int a, long b) {{ }}
             static void M(long a, int b) {{ }}
             static void N(Animal a, Dog b) {{ }}
             static void N(Dog a, Animal b) {{ }}
             static void O(IA a) {{ }}
             static void O(IB b) {{ }}
             static void P(object a, string b) {{ }}
             static void P(string a, object b) {{ }}
             static void Q(int a, double b) {{ }}
             static void Q(double a, int b) {{ }}
             static void Q(double a, double b) {{ }}
             static void R(long a, long b) {{ }}
             static void R(int a, long b) {{ }}
             static void R(long a, int b) {{ }}
             static void R(int a, int b) {{ }}
             static void S(byte a, long b) {{ }}
             static void S(long a, byte b) {{ }}
             static void T(int a, long b, int c = 0) {{ }}
             static void T(long a, int b) {{ }}
             static void U(params int[] xs) {{ }}
             static void U(int a, long b) {{ }}
             static void U(long a, int b) {{ }}
             static void V<T>(T a, long b) {{ }}
             static void V(long a, int b) {{ }}
             static void X(float a, double b) {{ }}
             static void X(double a, float b) {{ }}
             void Inst(Animal a, Dog b) {{ }}
             void Inst(Dog a, Animal b) {{ }}
             void Test(int i, long l, Dog d, Puppy p, AB ab, string s, byte by, short sh, float f, Animal an) {{ {body} }}
         }}"
    )
}

#[test]
fn a_call_two_overloads_take_equally_well_is_cs0121() {
    // The first declared was called, without a word that the other could
    // have been meant.
    assert_eq!(
        diagnose(&overloaded("M(i, i);")),
        [
            "CS0121 'M': The call is ambiguous between the following methods or properties: 'C.M(int, long)' and 'C.M(long, int)'"
        ]
    );
    for call in [
        // One argument is better for this one, the other for that one.
        "M(1, 1);",
        "N(d, d);",
        "N(p, p);",
        "P(s, s);",
        "Q(i, i);",
        "S(by, by);",
        "S(1, 1);",
        "X(f, f);",
        "X(1, 1);",
        "Inst(d, d);",
        "this.Inst(p, p);",
        "new C().Inst(d, d);",
        // Neither is better, and they are not the same.
        "O(ab);",
    ] {
        assert_eq!(only(&overloaded(call), &["CS0121"]), ["CS0121"], "{call}");
    }
}

#[test]
fn a_call_one_overload_takes_best_is_not_cs0121() {
    for call in [
        // One is better at an argument and no worse at any.
        "M(i, l); M(l, i); M(sh, l);",
        "N(an, d); N(d, an);",
        "P(s, 1); P(1, s);",
        "S(by, l); X(f, 1.0); Inst(an, d);",
        // A third is better than both.
        "R(i, i);",
        // Rules of their own, and Roslyn settles them: a default left
        // unfilled, an expanded `params`.
        "T(i, i);",
        "U(i, i);",
    ] {
        let found = only(&overloaded(call), &["CS0121"]);
        assert!(found.is_empty(), "{call}: {found:?}");
    }
}
