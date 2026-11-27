//! Code that Roslyn accepts, in the shapes that used to be reported as wrong
//! or that overflowed the stack. Every case here was put to Roslyn, and none
//! of them has a diagnostic.

use rustlyn_semantics::Compilation;
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

/// The codes of every error a file gets.
fn errors(source: &str) -> Vec<String> {
    let compilation = Compilation::create(vec![parse(SourceText::new("Program.cs", source))]);
    compilation
        .source_diagnostics()
        .into_iter()
        .map(|entry| entry.diagnostic.clone())
        .chain(
            compilation
                .semantic_diagnostics()
                .into_iter()
                .map(|entry| entry.diagnostic),
        )
        .filter(|diagnostic| diagnostic.is_error())
        .map(|diagnostic| diagnostic.code().to_string())
        .collect()
}

fn clean(source: &str) {
    assert_eq!(errors(source), Vec::<String>::new(), "{source}");
}

// MARK: - a default value that names its own method

#[test]
fn a_default_value_naming_its_own_method_ends() {
    // Binding the default needs the method group's type, which needs the
    // signature, which needs the default.
    errors("class C { void M(object a = new[] { M }) { } }");
    errors("class C { void M(object a = new object[] { M }) { } }");
    errors("class C { void M(object a = M) { } }");
    errors(
        "class C { void M(object a = new[] { N }) { } void N(object b = new[] { M }) { } void M() { } }",
    );
    errors("class C { void M() { void F(object a = new[] { F }) { } } }");
}

#[test]
fn nameof_of_the_method_is_a_default_value() {
    clean("class C { void M(string a = nameof(M)) { } }");
}

// MARK: - names in the attributes of local functions and lambdas

#[test]
fn an_attribute_on_a_local_function_names_a_constant_of_the_method() {
    clean(
        "using System;
         class A : Attribute { public A(int p) { } public int Prop { get; set; } }
         class Program {
             static void Main() {
                 const int N = 10;
                 void F([A(N)] int x) { }
                 [A(N, Prop = N)][return: A(N)] int G() => N;
                 F(1); G();
             }
         }",
    );
}

#[test]
fn an_attribute_on_a_lambda_names_a_constant_of_the_method() {
    clean(
        "using System;
         class A : Attribute { public A(int p) { } public int Prop { get; set; } }
         class Program {
             static void Main() {
                 const int N = 10;
                 var lam = [A(N, Prop = N)] ([A(Prop = N)] int x) => x;
                 lam(1);
             }
         }",
    );
}

#[test]
fn an_attribute_on_a_local_function_naming_nothing_is_still_wrong() {
    assert_eq!(
        errors(
            "using System;
             class A : Attribute { public A(int p) { } }
             class Program { static void Main() { [A(Missing)] void F() { } F(); } }"
        ),
        vec!["CS0103"]
    );
}

// MARK: - definite assignment

#[test]
fn a_struct_of_empty_structs_is_assigned_where_declared() {
    clean(
        "struct S { }
         struct T { S s1, s2, s3; static T M() { T t; return t; } }",
    );
}

#[test]
fn a_struct_with_a_field_is_not() {
    assert_eq!(
        errors("struct S { int x; } class C { S M() { S s; return s; } }"),
        vec!["CS0165"]
    );
}

#[test]
fn a_conditional_access_on_a_constant_always_runs_its_call() {
    clean(
        "class C {
             void M() {
                 int x, y;
                 _ = \"a\"?.Equals(x = y = 0) == true ? x.ToString() : y.ToString();
             }
         }",
    );
}

#[test]
fn a_cast_conditional_access_coalesced_with_a_throw_ran_its_call() {
    clean(
        "class C {
             void M1(C c1) {
                 int x;
                 _ = (object)c1?.M(x = 0) ?? throw new System.Exception();
                 x.ToString();
             }
             C M(object obj) { return this; }
         }",
    );
}

#[test]
fn a_type_test_or_bool_pattern_of_a_conditional_access_ran_the_call() {
    // `x` is assigned wherever the test holds, `y` is not.
    assert_eq!(
        errors(
            "class C {
                 C M0(object obj) => this;
                 bool B(object obj) => false;
                 void M1(C c) {
                     int x, y;
                     _ = c?.M0(x = y = 0) is C ? x.ToString() : y.ToString();
                 }
                 void M2(C c) {
                     int x, y;
                     _ = c?.B(x = y = 0) is true or false ? x.ToString() : y.ToString();
                 }
             }"
        ),
        vec!["CS0165", "CS0165"]
    );
}

#[test]
fn a_nullable_struct_compared_with_null_after_a_conditional_access() {
    assert_eq!(
        errors(
            "struct S {
                 public S M0(out int x, out int y) { x = 1; y = 1; return this; }
                 public void M1(S? s) {
                     int x, y;
                     _ = s?.M0(out x, out y) != null ? x.ToString() : y.ToString();
                 }
             }"
        ),
        vec!["CS0165"]
    );
}

// MARK: - expression variables

#[test]
fn a_variable_of_the_receiver_is_in_scope_in_the_arguments_of_the_call() {
    clean(
        "public class C {
             public C(out int x) { x = 0; }
             public C(bool b) { }
             C M0(C c) => c;
             C M1(int x) => null;
             bool TP(out int x) { x = 0; return true; }
             void M(int a) {
                 M0(new(out var x)).M1(x);
                 M0(new C(a is var y)).M1(y);
                 M0(new C(a is var z)).M1(z);
                 M0(null).M1(TP(out var w) ? w : 0);
             }
         }",
    );
}

#[test]
fn variables_of_a_target_typed_new_are_in_scope_after_it() {
    clean(
        "public class C {
             public C(bool x) { }
             void M(int a) {
                 M2(new(a is var x), x);
                 M2(new(GetBool(a is var y)), y);
             }
             void M2(C c, int x) { }
             bool GetBool(bool x) => x;
         }",
    );
}

// MARK: - names

#[test]
fn a_member_that_cannot_be_called_does_not_hide_a_method_further_out() {
    clean(
        "class A {
             delegate void D();
             static void Goo() { }
             class B {
                 const int Goo = 123;
                 static void Main() { Goo(); Bar(Goo); }
                 static void Bar(int x) { }
                 static void Bar(D x) { }
             }
         }",
    );
    clean(
        "class A {
             static void Goo(object x) { }
             class B {
                 class Goo { public const int N = 3; }
                 static void Main() { Goo(Goo.N); }
             }
         }",
    );
}

#[test]
fn a_name_with_type_arguments_is_no_local() {
    clean(
        "struct @var<T> { public static T field; }
         class Program {
             static void Main() { var var = \"A\"; var xs = var<int>.field; }
         }",
    );
}

#[test]
fn a_generic_attribute_is_found_by_its_arity() {
    clean(
        "using System;
         class MarkAttribute<T> : Attribute { }
         [Mark<int>] class C { }",
    );
}

// MARK: - types

#[test]
fn a_pointer_minus_null_is_a_pointer_difference() {
    clean(
        "unsafe class C { long M(int* p) { return p - null; } long N(int* p) { return null - p; } }",
    );
}

#[test]
fn a_covariant_return_is_the_overriding_type() {
    clean(
        "public class Base { public virtual object M() => null; public virtual object P => null; }
         public class Derived : Base { public override string M() => null; public override string P => null; }
         public class Program : Derived {
             string A(Derived d) { return d.M(); }
             string B(Derived d) { return d.P; }
             string C() { return M(); }
         }",
    );
    assert_eq!(
        errors(
            "public class Base { public virtual object M() => null; }
             public class Derived : Base { public override string M() => null; }
             public class Program { string A(Base b) { return b.M(); } }"
        ),
        vec!["CS0266"]
    );
}

#[test]
fn an_override_keeps_the_struct_constraint_of_what_it_overrides() {
    clean(
        "class A { public virtual T? Goo<T>() where T : struct { return null; } }
         class B : A { public override T? Goo<T>() { return null; } }",
    );
    clean(
        "abstract class Base { public abstract void Goo<T>(T? value) where T : struct; }
         class Derived : Base { public override void Goo<T>(T? value) { } }",
    );
}

#[test]
fn dynamic_and_object_bounds_are_one_type_to_inference() {
    clean(
        "class C {
             static void Main() {
                 object o = null; dynamic d = null;
                 var doc = (new[] { ((a: d, b: o), c: 2) }).ToList2();
                 var odc = (new[] { ((a: o, b: d), c: 2) }).ToList2();
                 var t1 = Test1(ref doc, odc);
                 var t2 = Test2(doc, ref odc);
                 var t3 = Test3(ref doc, ref odc);
             }
             static T Test1<T>(ref T x, T y) => x;
             static T Test2<T>(T x, ref T y) => x;
             static T Test3<T>(ref T x, ref T y) => x;
         }
         static class X { public static T[] ToList2<T>(this T[] a) => a; }",
    );
}

#[test]
fn function_pointer_types_are_inferred_through() {
    clean(
        "unsafe class C {
             public void M1<T>(delegate*<T, void> param) { }
             public void M2<T>(delegate*<T> param) { }
             public void M3<T>(delegate*<T, T> param) { }
             public void M() {
                 delegate*<string, void> p = null;
                 M1(p);
                 delegate*<string> q = null;
                 M2(q);
                 delegate*<int, int> r = null;
                 M3(r);
             }
         }",
    );
}

#[test]
fn function_pointer_inference_follows_the_variance_of_reference_types() {
    clean(
        "unsafe class C {
             public void M1<T>(delegate*<T, void> a, delegate*<T, void> b) { }
             public void M2<T>(delegate*<T> a, delegate*<T> b) { }
             public void M() {
                 delegate*<string, void> p1 = null;
                 delegate*<object, void> p2 = null;
                 M1(p1, p2);
                 delegate*<string> q1 = null;
                 delegate*<object> q2 = null;
                 M2(q1, q2);
             }
         }",
    );
    assert_eq!(
        errors(
            "unsafe class C {
                 public void M1<T>(delegate*<T, void> a, delegate*<T, void> b) { }
                 public void M() {
                     delegate*<int*, void> p3 = null;
                     delegate*<void*, void> p4 = null;
                     M1(p3, p4);
                 }
             }"
        ),
        vec!["CS0411"]
    );
}

#[test]
fn function_pointers_differing_in_object_and_dynamic_are_one_signature() {
    clean(
        "unsafe class Base {
             protected virtual void M1(delegate*<dynamic> ptr) { }
             protected virtual delegate*<object, void> M4() => throw null;
         }
         unsafe class Derived : Base {
             protected override void M1(delegate*<object> ptr) { }
             protected override delegate*<dynamic, void> M4() => throw null;
         }",
    );
}

#[test]
fn constants_in_a_collection_expression_reach_a_byte_parameter_of_an_extension() {
    clean(
        "class Foo { }
         static class E { public static bool Eq(this Foo s, byte[] o) => true; }
         class C { void M(Foo f) { f.Eq([0, 1]); } }",
    );
}

// MARK: - syntax

#[test]
fn an_enum_may_have_no_body() {
    clean("enum Figure; enum Other : int;");
}

#[test]
fn partial_before_a_name_and_a_semicolon_is_a_type() {
    clean(
        "partial class EnumPartial {
             internal enum @partial { }
             partial M;
         }",
    );
}

#[test]
fn an_event_may_have_an_empty_nested_initializer() {
    clean(
        "class Program {
             public event System.Action F;
             static Program M() => new Program() { F = { } };
         }",
    );
}

#[test]
fn an_out_variable_of_with_is_in_scope_in_the_elements() {
    clean("class C { void M() { int[] a = [with(out var x), x, x + 1]; } }");
}

// MARK: - `dynamic` beside another type

#[test]
fn a_conditional_with_a_dynamic_branch_is_dynamic_whichever_comes_first() {
    // The type was the first branch's where that converted to the other's,
    // so `flag ? text : dyn` was a `string` and the call on it was bound at
    // compile time (and failed at run time); `flag ? dyn : text` was right.
    clean(
        "class C {
             void M(bool flag, object o, string s, dynamic d, int i) {
                 var a = flag ? o : d; int a1 = a.Length;
                 var b = flag ? d : o; int b1 = b.Length;
                 var c = flag ? s : d; int c1 = c.Missing();
                 var e = flag ? i : d; int e1 = e.Missing;
                 var f = flag ? null : d; int f1 = f.Missing;
             }
         }",
    );
}

#[test]
fn the_best_common_type_with_a_dynamic_among_the_elements_is_dynamic() {
    clean(
        "class C {
             void M(bool flag, object o, string s, dynamic d, int i) {
                 var a = new[] { o, d }; int a1 = a[0].Length;
                 var b = new[] { d, o }; int b1 = b[0].Length;
                 var c = new[] { s, d }; int c1 = c[1].Missing;
                 var e = new[] { i, d }; int e1 = e[0].Missing;
                 var f = flag switch { true => o, _ => d }; int f1 = f.Length;
                 var g = flag switch { true => d, _ => o }; int g1 = g.Length;
             }
         }",
    );
}

#[test]
fn a_lambda_that_gives_back_a_dynamic_value_has_that_type_to_inference() {
    // The conversion of the body to the `object` the probe asks for took the
    // `dynamic` with it, so `T` was inferred as `object` and `a.Length` was
    // reported as missing.
    clean(
        "class C {
             static T Make<T>(System.Func<T> f) => f();
             static T Apply<A, T>(A a, System.Func<A, T> f) => f(a);
             void M(dynamic d, object o, bool flag) {
                 var a = Make(() => (dynamic)\"abc\"); int a1 = a.Length;
                 var b = Make(() => d); int b1 = b.Length;
                 var c = Apply(1, x => (dynamic)x); int c1 = c.Missing;
                 var e = Make(() => { if (flag) return o; return d; }); int e1 = e.Length;
                 var f = Make(() => { if (flag) return d; return o; }); int f1 = f.Length;
                 var g = Make(() => flag ? o : d); int g1 = g.Length;
             }
         }",
    );
}

#[test]
fn a_lambda_that_gives_back_an_object_stays_an_object() {
    assert_eq!(
        errors(
            "class C {
                 static T Make<T>(System.Func<T> f) => f();
                 void M(object o) {
                     var a = Make(() => o); int a1 = a.Length;
                     var b = Make(() => (object)\"abc\"); int b1 = b.Length;
                 }
             }"
        ),
        ["CS1061", "CS1061"]
    );
}

// MARK: - `+` and `-` on delegates

#[test]
fn a_delegate_combined_with_a_lambda_or_a_method_group_takes_the_delegates_type() {
    clean(
        "class C {
             static void Log(int x) { }
             static int One() => 1;
             void M() {
                 System.Action<int> a = x => { };
                 System.Action<int> b = a + (x => Log(x));
                 System.Action<int> c = (x => Log(x)) + a;
                 System.Action<int> d = a + Log;
                 System.Action<int> e = Log + a;
                 System.Action<int> f = a - Log;
                 System.Action<int> g = a + delegate (int x) { };
                 System.Func<int> h = One;
                 System.Func<int> i = h + (() => 2);
                 var j = a + (x => Log(x));
                 object k = a - (x => { });
                 a += x => Log(x);
                 a -= Log;
             }
         }",
    );
}

#[test]
fn a_delegate_combined_with_what_cannot_be_it_is_an_operator_error() {
    // Two functions say nothing to each other, and a lambda with another
    // number of parameters than the delegate cannot be the delegate.
    assert_eq!(
        errors(
            "class C {
                 static void Log(int x) { }
                 void M() {
                     System.Action<int> a = x => { };
                     var b = (x => { }) + (y => { });
                     var c = a + (() => { });
                     var d = Log + Log;
                     var e = a + ((x, y) => { });
                 }
             }"
        ),
        ["CS0019", "CS0019", "CS0019", "CS0019"]
    );
}

// MARK: - `is` patterns that take every value

#[test]
fn a_pattern_that_takes_every_value_leaves_nothing_unassigned() {
    // `or` of what does not match and what does covers the input, which
    // Roslyn knows, and the `else` it implies is never taken.
    clean(
        "class C {
             void M(object o, int? ni, string s, int n, bool? nb, byte by, N link) {
                 int a; if (ni is int or null) a = 1; Use(a);
                 int b; if (o is string or not string) b = 1; Use(b);
                 int c; if (s is null or not null) c = 1; Use(c);
                 int d; if (o is object or null) d = 1; Use(d);
                 int e; if (o is not null or null) e = 1; Use(e);
                 int f; if (ni is { } or null) f = 1; Use(f);
                 int g; if (ni is null or int) g = 1; Use(g);
                 int h; if (s is object or null) h = 1; Use(h);
                 int i; if (o is not object or object) i = 1; Use(i);
                 int j; if ((o is string or not string) && true) j = 1; Use(j);
                 int k; if (ni is int or not int) k = 1; Use(k);
                 int l; if (nb is true or false or null) l = 1; Use(l);
                 int m; if (n is < 0 or >= 0) m = 1; Use(m);
                 int p; if (ni is (< 0 or >= 0) or null) p = 1; Use(p);
                 int q; if (by is >= 0 and <= 255) q = 1; Use(q);
                 int r; if (n is (> 0 and < 10) or not (> 0 and < 10)) r = 1; Use(r);
                 int t; if (link is { Next: null } or { Next: not null } or null) t = 1; Use(t);
             }
             static void Use(int x) { }
         }
         class N { public N Next; }",
    );
}

#[test]
fn a_pattern_that_may_miss_a_value_still_leaves_a_variable_unassigned() {
    // Each of these takes everything but one kind of value, and the use after
    // it is CS0165 in Roslyn.
    for pattern in [
        "ni is int",
        "ni is null",
        "ni is not null",
        "o is string",
        "o is string or int",
        "o is not null",
        "s is object",
        "s is string",
        "s is not null or \"a\"",
        "o is not int and not null or null",
        "ni is int or not null",
        "ni is (> 0 or < 0) or null",
        "ni is (> 0 or < 0)",
        "by is >= 0 and < 255",
        "link is { Next: null } or { Next: not null }",
        "link is { Next: null } or null",
    ] {
        assert_eq!(
            errors(&format!(
                "class C {{
                     void M(object o, int? ni, string s, byte by, N link) {{
                         int r; if ({pattern}) r = 1; Use(r);
                     }}
                     static void Use(int x) {{ }}
                 }}
                 class N {{ public N Next; }}"
            )),
            ["CS0165"],
            "{pattern}"
        );
    }
}

/// A `switch` expression on the right of a compound assignment goes to the
/// type on the left arm by arm, as it does in a plain assignment: the arms
/// alone would make an `int`, and judging that `int` against a `byte` was a
/// CS0266 Roslyn does not report. A conditional has a type of its own, and
/// is judged by it.
#[test]
fn a_switch_expression_on_the_right_of_a_compound_assignment_is_not_judged_by_its_arms() {
    clean(
        "enum K { A, B }
         class C {
             void M(K k, byte b, short s, sbyte sb) {
                 b |= k switch { K.A => 1, K.B => 0, _ => 2 };
                 b += k switch { K.A => 1, _ => 2 };
                 s *= k switch { K.A => 3, _ => 4 };
                 sb ^= (k switch { K.A => 1, _ => 2 });
             }
         }",
    );
    assert_eq!(
        errors(
            "class C {
                 void M(bool f, byte b) {
                     b |= f ? 1 : 0;
                 }
             }"
        ),
        ["CS0266"]
    );
}

// MARK: - the target of a null-conditional assignment

#[test]
fn the_target_of_a_null_conditional_assignment_is_written_and_not_read() {
    // `x?.F += 3;` has no value to hand back, so a `T` that cannot be made nullable is no
    // trouble; where the value of the assignment is used (`var r = x?.F += 2;`) it is CS8978.
    clean(
        "interface I1 { void operator +=(int x); }
         class C2<T> where T : I1 { public T F; }
         class P {
             static void M<T>(C2<T> x) where T : I1 { x?.F += 3; x?.F = default; }
         }",
    );
    assert_eq!(
        errors(
            "interface I1 { void operator +=(int x); }
             class C2<T> where T : I1 { public T F; }
             class P {
                 static void M<T>(C2<T> x) where T : I1 { var r = x?.F += 2; }
             }"
        ),
        ["CS8978"]
    );
}

// MARK: - instance operators

#[test]
fn an_instance_operator_is_called_on_a_variable_and_a_static_one_where_there_is_none() {
    clean(
        "class K {
             public int F;
             public void operator +=(int x) { F += x; }
             public void operator ++() { F++; }
             public void operator checked --() { F--; }
             public void operator --() { F--; }
         }
         struct S {
             public static S operator +(S a, int b) => a;
             public void operator ++() { }
             public void Self() { this += 1; ++this; }
         }
         class P {
             K k = new K(); S s; K[] ks = new K[1];
             void M(ref S r) { k += 1; ++k; k++; ks[0] += 2; s += 1; ++s; s++; r += 1; checked { --k; } var a = k += 1; var b = s += 2; }
         }",
    );
}

// MARK: - local functions, conversions and queries that were reported as wrong

#[test]
fn a_generic_local_function_infers_its_type_parameter_from_a_lambda_argument() {
    // `U Conv<U>(F<int, U> f)` called with `x => x + 1` is `Conv<int>`, as a method of that shape
    // is: the call was resolved on the types of the arguments alone, which a lambda has none of.
    clean(
        r#"delegate R F<A, R>(A a);
         delegate void G<A>(A a);
         class Gen<T> {
             public int Run(T seed) {
                 U Conv<U>(F<T, U> f) => f(seed);
                 return Conv(x => 5);
             }
         }
         class P {
             static int A() { U Conv<U>(F<int, U> f) => f(1); return Conv(x => x + 1); }
             static string B() { var r = Conv(x => "s"); return r; static U Conv<U>(F<int, U> f) => f(7); }
             static int C() {
                 int Outer() {
                     V Twice<V>(F<int, V> f, F<V, V> g) => g(f(0));
                     return Twice(i => 3, v => v * 2);
                 }
                 return Outer();
             }
             static int D() {
                 R Map<S, R>(S s, F<S, R> f) => f(s);
                 void Do<X>(X x, G<X> a) { a(x); }
                 Do(5, v => { });
                 return Map(4, x => x + 1) + Map("ab", s => 1);
             }
         }"#,
    );
}

#[test]
fn a_user_defined_conversion_is_followed_by_a_lifted_standard_one() {
    // §10.5.4: the second step of a user-defined implicit conversion is any standard implicit
    // conversion, `int?` to `long?` and `double?` among them, and an `S?` is lifted over an
    // operator that gives a nullable itself.
    clean(
        "class N1 { public static implicit operator int?(N1 n) { return 5; } }
         class N2 { public static implicit operator int(N2 n) { return 6; } }
         struct S1 { public static implicit operator int?(S1 n) { return 8; } }
         struct S2 { public static implicit operator int(S2 n) { return 9; } }
         class N3 { public static implicit operator int?(N3 n) { return 5; } public static implicit operator long(N3 n) { return 55; } }
         class P {
             static void Main() {
                 long? a = new N1(); double? b = new N1(); long? c = new N2(); double? d = new N2();
                 S1 s1 = default(S1); S1? n1 = s1; long? e = s1; long? f = n1; double? g = n1;
                 S2? n2 = new S2(); long? h = n2; long? i = new N3();
             }
         }",
    );
}

#[test]
fn a_select_after_a_second_from_needs_only_select_many() {
    // The `select` is the result selector of the `SelectMany` (§12.20.3), so a type that has no
    // `Select` still has a query of two `from`s ending in one.
    clean(
        "delegate R F<A, R>(A a);
         delegate R F2<A, B, R>(A a, B b);
         class Box<T> {
             public Box<V> SelectMany<U, V>(F<T, Box<U>> f, F2<T, U, V> r) { return null; }
         }
         class P {
             static void M(Box<int> a, Box<string> b) {
                 var q = from x in a from y in b select x + y;
                 var r = from x in a from y in b from z in a select y + z;
             }
         }",
    );
}

#[test]
fn a_class_deriving_from_a_construction_of_itself_is_bound_and_ends() {
    // `class A<T> : A<A<T>>` is circular (CS0146 in Roslyn); each base of it is a new type, and
    // whatever walks them has to stop. A curiously recurring base is not circular.
    let _ = errors(
        "class A<T> : A<A<T>> { } class P { static void Main() { A<int> a = new A<int>(); } }",
    );
    let _ = errors("class A<T> : B<T> { } class B<T> : C<B<T>> { } class C<T> : A<C<T>> { }");
    clean(
        "class Base<T> { }
         class L<T> : Base<L<L<T>>> { }
         abstract class E<TSelf> where TSelf : E<TSelf> { public TSelf Me { get { return (TSelf)this; } } }
         sealed class F : E<F> { }
         class Outer<T> { public class B : Outer<B> { } }
         class P { static void Main() { object o = new F().Me; } }",
    );
}

// MARK: - a member of the name of a primary constructor parameter

#[test]
fn a_member_of_the_name_of_a_primary_constructor_parameter_is_what_a_method_reads() {
    // In a method or accessor the type's member, declared or inherited, comes before the
    // parameter (C# 12): `static int x` read by a static method is no use of the parameter,
    // which a static member cannot use; the parameter wins in initializers and in the base
    // constructor's arguments.
    clean(
        "class S(int x) { static int x = 5; static int G() => x; }
         class M(string name) { public static string name() => \"m\"; public static string Call() => name(); }
         class B(int v) { protected int v = v; }
         class D(int v) : B(v) { public int Get() => v; public int Init = v; }
         class T1(int a) { int a = a; public void Inc() { a++; a += 2; a = a * 2; } public int Get() => a; }
         class T3(int p) { public int P { get; } = p; public int Q() { int p = 2; return p; } }
         struct SS(int s) { int s = s; public int Next() => ++s; }",
    );
}

// MARK: - constraints that are not conversions

#[test]
fn a_generic_candidate_whose_new_or_unmanaged_constraint_fails_leaves_the_other() {
    clean(
        "struct W<T> { public T x; }
         abstract class Abs { }
         class P {
             static int Pick<T>(T t) where T : new() { return 1; }
             static int Pick(object o) { return 2; }
             static int Un<T>(T t) where T : unmanaged { return 1; }
             static int Un(object o) { return 2; }
             static int E<T>(System.Collections.Generic.List<T> l) where T : new() { return 1; }
             static int E(System.Collections.Generic.IEnumerable<object> l) { return 2; }
             static void Main(Abs abs, string s, W<string> w) {
                 int a = Pick(s) + Pick(1) + Pick(abs) + Pick(new int[0]) + Un(s) + Un(1) + Un(w);
                 int b = E(new System.Collections.Generic.List<string>());
             }
         }",
    );
}

// MARK: - a string joined to a type with a plus of its own

#[test]
fn a_string_joined_to_a_type_with_a_plus_that_does_not_take_it_is_concatenated() {
    clean(
        "struct Tk {
             public static implicit operator string(Tk t) { return \"c\"; }
             public static string operator +(Tk a, string b) { return b; }
         }
         class P { static void Main() { Tk t = default(Tk); string a = \"a\" + t; string b = t + \"a\"; string c = \"a\" + t + \"a\"; string d = \"x\"; d += t; } }",
    );
}

// MARK: - `union` as a name, under the released language version

#[test]
fn union_is_a_name_where_no_language_version_is_given() {
    // C# 15's unions are read only where the version is named: the default is the newest
    // released version, C# 14, which has no `union` keyword.
    clean(
        "class union { }
         class P { static union Make() { union u = new union(); return u; } static void Main() { var x = Make(); } }",
    );
}
