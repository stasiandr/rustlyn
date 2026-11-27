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
