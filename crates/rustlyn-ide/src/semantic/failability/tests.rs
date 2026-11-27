//! Failability on code that grows step by step: a `throw`, its condition,
//! constants, callers, fields, calls into other members.

use std::path::Path;

use super::super::tests::compile;
use super::{Failability, FailureKind, Origin, Verdict};

/// The failability of the member whose name follows `marker` in `text`.
fn failability(text: &str, marker: &str) -> Failability {
    let semantic = compile(&[("C.cs", text)], false).expect("compiles");
    let at = text.find(marker).expect("marker") + marker.len();
    semantic
        .failability(Path::new("/p/C.cs"), at as u32)
        .expect("a member")
}

fn verdicts(found: &Failability) -> Vec<(String, Verdict)> {
    found
        .failures
        .iter()
        .map(|f| (f.exception.clone(), f.verdict))
        .collect()
}

#[test]
fn a_method_without_throws_cannot_fail() {
    let found = failability(
        "class C { int Add(int a, int b) { return a + b; } }",
        "int ",
    );
    assert_eq!(found.member, "C.Add");
    assert!(found.failures.is_empty(), "{found:?}");
}

#[test]
fn an_unconditional_throw_always_fails() {
    let found = failability(
        "class C { void Run() { throw new System.InvalidOperationException(\"not yet\"); } }",
        "void ",
    );
    let [failure] = found.failures.as_slice() else {
        panic!("{found:?}")
    };
    assert_eq!(failure.kind, FailureKind::Throw);
    assert_eq!(failure.exception, "InvalidOperationException");
    assert_eq!(failure.message.as_deref(), Some("not yet"));
    assert_eq!(failure.verdict, Verdict::Always);
    assert!(failure.conditions.is_empty());
}

#[test]
fn a_guard_is_the_condition() {
    let text = "using System;\nclass C {\n    public void Pay(int amount) {\n        if (amount < 0) throw new ArgumentException(\"negative\");\n    }\n}";
    let found = failability(text, "void ");
    let [failure] = found.failures.as_slice() else {
        panic!("{found:?}")
    };
    let conditions: Vec<&str> = failure.conditions.iter().map(|c| c.text.as_str()).collect();
    assert_eq!(conditions, ["amount < 0"]);
    // Nobody calls it: what `amount` is is not known.
    assert_eq!(failure.verdict, Verdict::Unknown);
    assert_eq!(failure.inputs[0].origin, Origin::NoCallers);
}

#[test]
fn an_early_return_negates_its_condition() {
    let text = "using System;\nclass C {\n    void Use(string name) {\n        if (name != null) return;\n        throw new ArgumentNullException(\"name\");\n    }\n}";
    let found = failability(text, "void ");
    let [failure] = found.failures.as_slice() else {
        panic!("{found:?}")
    };
    let conditions: Vec<&str> = failure.conditions.iter().map(|c| c.text.as_str()).collect();
    assert_eq!(conditions, ["name == null"]);
}

#[test]
fn a_constant_argument_makes_the_throw_unreachable() {
    let text = "using System;\nclass C {\n    void Pay(int amount) {\n        if (amount < 0) throw new ArgumentException(\"negative\");\n    }\n    void Buy() { Pay(5); }\n    void Sell() { Pay(10); }\n}";
    let found = failability(text, "void ");
    let [failure] = found.failures.as_slice() else {
        panic!("{found:?}")
    };
    assert_eq!(failure.verdict, Verdict::Never, "{failure:?}");
    let input = &failure.inputs[0];
    assert_eq!(input.name, "amount");
    assert_eq!(input.origin, Origin::Callers { count: 2 });
    assert_eq!(
        input.values.as_deref(),
        Some(&["5".to_owned(), "10".to_owned()][..])
    );
}

#[test]
fn one_bad_caller_makes_it_possible() {
    let text = "using System;\nclass C {\n    void Pay(int amount) {\n        if (amount < 0) throw new ArgumentException(\"negative\");\n    }\n    void Buy() { Pay(5); }\n    void Refund() { Pay(-3); }\n}";
    let found = failability(text, "void ");
    assert_eq!(
        verdicts(&found),
        [("ArgumentException".to_owned(), Verdict::Possible)]
    );
}

#[test]
fn every_caller_passing_a_bad_value_makes_it_always() {
    let text = "using System;\nclass C {\n    void Pay(int amount) {\n        if (amount < 0) throw new ArgumentException(\"negative\");\n    }\n    void Refund() { Pay(-3); }\n}";
    let found = failability(text, "void ");
    assert_eq!(
        verdicts(&found),
        [("ArgumentException".to_owned(), Verdict::Always)]
    );
}

#[test]
fn constants_and_arithmetic_at_the_call_are_followed() {
    let text = "using System;\nclass C {\n    const int Price = 7;\n    void Pay(int amount) {\n        if (amount <= 0) throw new ArgumentException();\n    }\n    void Buy() { Pay(Price * 2 - 1); }\n}";
    let found = failability(text, "void Pay");
    assert_eq!(
        verdicts(&found),
        [("ArgumentException".to_owned(), Verdict::Never)]
    );
}

#[test]
fn a_readonly_field_set_in_the_constructor() {
    let text = "using System;\nclass C {\n    readonly int limit;\n    C() { limit = 10; }\n    void Check() {\n        if (limit > 100) throw new InvalidOperationException(\"too big\");\n    }\n}";
    let found = failability(text, "void ");
    let [failure] = found.failures.as_slice() else {
        panic!("{found:?}")
    };
    assert_eq!(failure.verdict, Verdict::Never, "{failure:?}");
    assert_eq!(failure.inputs[0].origin, Origin::Writes { readonly: true });
    assert_eq!(
        failure.inputs[0].values.as_deref(),
        Some(&["10".to_owned()][..])
    );
}

#[test]
fn a_field_with_an_initializer_and_no_writes() {
    let text = "using System;\nclass C {\n    int count = 3;\n    void Check() {\n        if (count == 0) throw new InvalidOperationException();\n    }\n}";
    let found = failability(text, "void ");
    assert_eq!(
        verdicts(&found),
        [("InvalidOperationException".to_owned(), Verdict::Never)]
    );
}

#[test]
fn a_field_nothing_writes_keeps_its_default() {
    let text = "using System;\nclass C {\n    int count;\n    void Check() {\n        if (count == 0) throw new InvalidOperationException();\n    }\n}";
    let found = failability(text, "void ");
    let [failure] = found.failures.as_slice() else {
        panic!("{found:?}")
    };
    assert_eq!(failure.verdict, Verdict::Always, "{failure:?}");
    assert_eq!(failure.inputs[0].origin, Origin::NeverWritten);
}

#[test]
fn a_field_written_elsewhere_with_any_value_is_unknown() {
    let text = "using System;\nclass C {\n    int count = 1;\n    public void Set(int value) { count = value; }\n    void Check() {\n        if (count == 0) throw new InvalidOperationException();\n    }\n}";
    let found = failability(text, "void Check");
    assert_eq!(
        verdicts(&found),
        [("InvalidOperationException".to_owned(), Verdict::Unknown)]
    );
}

#[test]
fn a_field_written_from_known_callers() {
    // The value written is a parameter, and its callers say what it is.
    let text = "using System;\nclass C {\n    int count = 1;\n    void Set(int value) { count = value; }\n    void Init() { Set(4); }\n    void Check() {\n        if (count == 0) throw new InvalidOperationException();\n    }\n}";
    let found = failability(text, "void Check");
    assert_eq!(
        verdicts(&found),
        [("InvalidOperationException".to_owned(), Verdict::Never)]
    );
}

#[test]
fn a_local_given_a_constant() {
    let text = "using System;\nclass C {\n    void Run() {\n        int retries = 3;\n        if (retries > 5) throw new InvalidOperationException();\n    }\n}";
    let found = failability(text, "void ");
    assert_eq!(
        verdicts(&found),
        [("InvalidOperationException".to_owned(), Verdict::Never)]
    );
}

#[test]
fn conditions_that_contradict_each_other() {
    let text = "using System;\nclass C {\n    void Pay(int amount) {\n        if (amount > 0) {\n            if (amount < 0) throw new ArgumentException();\n        }\n    }\n    void A() { Pay(1); }\n    void B() { Pay(-1); }\n}";
    let found = failability(text, "void Pay");
    assert_eq!(
        verdicts(&found),
        [("ArgumentException".to_owned(), Verdict::Never)]
    );
}

#[test]
fn a_failure_in_a_called_method_with_its_argument() {
    let text = "using System;\nclass C {\n    void Withdraw(int amount) {\n        if (amount < 0) throw new ArgumentException(\"negative\");\n    }\n    void Pay() { Withdraw(5); }\n    void Refund() { Withdraw(-5); }\n}";
    let pay = failability(text, "void Pay");
    let [failure] = pay.failures.as_slice() else {
        panic!("{pay:?}")
    };
    assert_eq!(failure.verdict, Verdict::Never, "{failure:?}");
    assert_eq!(failure.chain.len(), 1);
    assert_eq!(failure.chain[0].callee, "C.Withdraw");
    assert_eq!(failure.inputs[0].origin, Origin::Argument);
    let refund = failability(text, "void Refund");
    assert_eq!(
        verdicts(&refund),
        [("ArgumentException".to_owned(), Verdict::Always)]
    );
}

#[test]
fn a_catch_stops_the_failure() {
    let text = "using System;\nclass C {\n    void Inner() { throw new ArgumentException(); }\n    void Outer() {\n        try { Inner(); } catch (ArgumentException) { }\n    }\n}";
    let found = failability(text, "void Outer");
    assert!(found.failures.is_empty(), "{found:?}");
}

#[test]
fn a_catch_of_another_type_does_not() {
    let text = "using System;\nclass C {\n    void Inner() { throw new ArgumentException(); }\n    void Outer() {\n        try { Inner(); } catch (NotSupportedException) { }\n    }\n}";
    let found = failability(text, "void Outer");
    assert_eq!(found.failures.len(), 1, "{found:?}");
}

#[test]
fn division_by_a_parameter() {
    let text = "class C {\n    int Ratio(int total, int parts) { return total / parts; }\n    int A() => Ratio(10, 2);\n}";
    let found = failability(text, "int Ratio");
    let [failure] = found.failures.as_slice() else {
        panic!("{found:?}")
    };
    assert_eq!(failure.kind, FailureKind::DivideByZero);
    assert_eq!(failure.conditions[0].text, "parts == 0");
    assert_eq!(failure.verdict, Verdict::Never);
}

#[test]
fn division_by_a_constant_is_not_a_failure() {
    let found = failability("class C { int Half(int x) { return x / 2; } }", "int ");
    assert!(found.failures.is_empty(), "{found:?}");
}

#[test]
fn a_coalesce_throw() {
    let text = "using System;\nclass C {\n    string name;\n    string Name() => name ?? throw new InvalidOperationException();\n}";
    let found = failability(text, "string Name");
    let [failure] = found.failures.as_slice() else {
        panic!("{found:?}")
    };
    assert_eq!(failure.conditions[0].text, "name == null");
    // Nothing writes `name`: it is null, and the throw always happens.
    assert_eq!(failure.verdict, Verdict::Always, "{failure:?}");
}

#[test]
fn a_virtual_method_does_not_trust_its_callers() {
    let text = "using System;\nclass C {\n    public virtual void Pay(int amount) {\n        if (amount < 0) throw new ArgumentException();\n    }\n    void Buy() { Pay(5); }\n}";
    let found = failability(text, "void Pay");
    let [failure] = found.failures.as_slice() else {
        panic!("{found:?}")
    };
    assert_eq!(failure.verdict, Verdict::Unknown);
    assert_eq!(failure.inputs[0].origin, Origin::Escapes);
}

#[test]
fn a_method_used_as_a_delegate_does_not_trust_its_callers() {
    let text = "using System;\nclass C {\n    void Pay(int amount) {\n        if (amount < 0) throw new ArgumentException();\n    }\n    void Buy() { Pay(5); Action<int> a = Pay; }\n}";
    let found = failability(text, "void Pay");
    assert_eq!(
        verdicts(&found),
        [("ArgumentException".to_owned(), Verdict::Unknown)]
    );
}

#[test]
fn a_switch_case_is_a_condition() {
    let text = "using System;\nclass C {\n    void Mode(int m) {\n        switch (m) {\n            case 1: break;\n            case 2: throw new NotSupportedException();\n        }\n    }\n    void A() { Mode(1); }\n}";
    let found = failability(text, "void Mode");
    let [failure] = found.failures.as_slice() else {
        panic!("{found:?}")
    };
    assert_eq!(failure.conditions[0].text, "m == 2");
    assert_eq!(failure.verdict, Verdict::Never);
}

// MARK: - failures the code does not write

#[test]
fn a_field_nothing_assigns_is_null_where_it_is_used() {
    let text = "class Item { public int Price; }\nclass C {\n    Item item;\n    int Price() { return item.Price; }\n}";
    let found = failability(text, "int Price()");
    let [failure] = found.failures.as_slice() else {
        panic!("{found:?}")
    };
    assert_eq!(failure.kind, FailureKind::NullReference);
    assert_eq!(failure.conditions[0].text, "item == null");
    assert_eq!(failure.verdict, Verdict::Always);
}

#[test]
fn a_field_given_an_object_is_not_null() {
    let text = "class Item { public int Price; }\nclass C {\n    readonly Item item = new Item();\n    int Price() { return item.Price; }\n}";
    let found = failability(text, "int Price()");
    assert!(found.failures.is_empty(), "{found:?}");
}

#[test]
fn an_unknown_receiver_is_not_a_finding() {
    let text = "class Item { public int Price; }\nclass C {\n    int Price(Item item) { return item.Price; }\n}";
    let found = failability(text, "int Price(");
    assert!(found.failures.is_empty(), "{found:?}");
}

#[test]
fn a_null_argument_reaches_the_dereference() {
    let text = "class Item { public int Price; }\nclass C {\n    int Price(Item item) { return item.Price; }\n    int A() => Price(null);\n    int B() => Price(new Item());\n}";
    let found = failability(text, "int Price(");
    assert_eq!(
        verdicts(&found),
        [("NullReferenceException".to_owned(), Verdict::Possible)]
    );
}

#[test]
fn a_null_check_guards_the_dereference() {
    let text = "class Item { public int Price; }\nclass C {\n    Item item;\n    int Price() { if (item == null) return 0; return item.Price; }\n}";
    let found = failability(text, "int Price()");
    assert!(found.failures.is_empty(), "{found:?}");
}

#[test]
fn an_index_past_a_known_array() {
    let text = "class C {\n    readonly int[] slots = new int[3];\n    int Get(int i) { return slots[i]; }\n    int A() => Get(1);\n    int B() => Get(3);\n}";
    let found = failability(text, "int Get(");
    let [failure] = found.failures.as_slice() else {
        panic!("{found:?}")
    };
    assert_eq!(failure.kind, FailureKind::IndexOutOfRange);
    assert_eq!(failure.verdict, Verdict::Possible);
}

#[test]
fn an_index_inside_a_known_array_is_not_a_finding() {
    let text = "class C {\n    readonly int[] slots = { 1, 2, 3 };\n    int Get(int i) { return slots[i]; }\n    int A() => Get(0) + Get(2);\n}";
    let found = failability(text, "int Get(");
    assert!(found.failures.is_empty(), "{found:?}");
}

#[test]
fn parse_of_a_constant_that_is_a_number() {
    let text = "class C {\n    int Read(string s) { return int.Parse(s); }\n    int A() => Read(\"42\");\n}";
    let found = failability(text, "int Read(");
    let [failure] = found.failures.as_slice() else {
        panic!("{found:?}")
    };
    assert_eq!(failure.exception, "FormatException");
    assert_eq!(failure.verdict, Verdict::Never);
}

#[test]
fn parse_of_a_constant_that_is_not() {
    let text = "class C {\n    int Read(string s) { return int.Parse(s); }\n    int A() => Read(\"forty\");\n}";
    let found = failability(text, "int Read(");
    assert_eq!(
        verdicts(&found),
        [("FormatException".to_owned(), Verdict::Always)]
    );
}

#[test]
fn a_dictionary_lookup_may_miss() {
    let text = "using System.Collections.Generic;\nclass C {\n    Dictionary<string, int> prices = new Dictionary<string, int>();\n    int Price(string name) { return prices[name]; }\n}";
    let found = failability(text, "int Price(");
    let [failure] = found.failures.as_slice() else {
        panic!("{found:?}")
    };
    assert_eq!(failure.exception, "KeyNotFoundException");
    assert_eq!(failure.verdict, Verdict::Unknown);
    assert_eq!(failure.conditions[0].text, "name is not in prices");
}

#[test]
fn a_dictionary_write_is_not_a_lookup() {
    let text = "using System.Collections.Generic;\nclass C {\n    Dictionary<string, int> prices = new Dictionary<string, int>();\n    void Set(string name) { prices[name] = 1; }\n}";
    let found = failability(text, "void Set(");
    assert!(found.failures.is_empty(), "{found:?}");
}

#[test]
fn contains_key_guards_the_lookup() {
    // The synthesised library has no `ContainsKey`: a dictionary of the
    // test's own stands in, in the namespace that makes it one.
    let text = "namespace System.Collections.Generic {\n    public class DictionaryLike<K, V> { public bool ContainsKey(K key) => true; public V this[K key] => default; }\n}\nclass C {\n    System.Collections.Generic.DictionaryLike<string, int> prices = new System.Collections.Generic.DictionaryLike<string, int>();\n    int Price(string name) { if (!prices.ContainsKey(name)) return 0; return prices[name]; }\n}";
    let found = failability(text, "int Price(");
    assert!(found.failures.is_empty(), "{found:?}");
}

#[test]
fn first_of_a_sequence() {
    let text = "using System.Collections.Generic;\nusing System.Linq;\nnamespace System.Linq { public static class Enumerable { public static extern T First<T>(this IEnumerable<T> source); public static extern bool Any<T>(this IEnumerable<T> source); } }\nclass C {\n    List<int> items = new List<int>();\n    int Head() { return items.First(); }\n    int Safe() { return items.Any() ? items.First() : 0; }\n}";
    let head = failability(text, "int Head");
    assert_eq!(
        verdicts(&head),
        [("InvalidOperationException".to_owned(), Verdict::Unknown)]
    );
    assert_eq!(head.failures[0].conditions[0].text, "items is empty");
    let safe = failability(text, "int Safe");
    assert!(safe.failures.is_empty(), "{safe:?}");
}

#[test]
fn a_property_getter_is_followed() {
    let text = "using System;\nclass C {\n    int Value { get { throw new NotSupportedException(); } }\n    int Read() { return Value + 1; }\n}";
    let found = failability(text, "int Read");
    assert_eq!(
        verdicts(&found),
        [("NotSupportedException".to_owned(), Verdict::Always)]
    );
    assert_eq!(found.failures[0].chain[0].callee, "C.Value");
}

#[test]
fn an_auto_property_set_once_is_known() {
    let text = "using System;\nclass C {\n    public int Max { get; } = 10;\n    void Check() { if (Max < 1) throw new InvalidOperationException(); }\n}";
    let found = failability(text, "void Check");
    assert_eq!(
        verdicts(&found),
        [("InvalidOperationException".to_owned(), Verdict::Never)]
    );
}

/// A conditional bound once to see whether it has a type of its own, and
/// thrown away, used to leave the pattern variable of its condition in
/// scope, pointing at a local that was gone: binding it again panicked.
#[test]
fn a_pattern_in_a_conditional_bound_twice() {
    let text = "class C { void M() { System.Action a = 1 is { } t ? () => Use(t) : null; } void Use(object o) {} }";
    let found = failability(text, "void M");
    assert!(found.failures.is_empty(), "{found:?}");
}

#[test]
fn a_body_that_does_not_bind_may_hide_a_write() {
    // `Missing.Run` does not resolve: whatever the body does, it is not
    // known, and the field may have been written there.
    let text = "using System;\nclass C {\n    int count = 1;\n    void Set() { Missing.Run(() => { count = 0; }); }\n    void M() { if (count == 0) throw new InvalidOperationException(); }\n}";
    let found = failability(text, "void M");
    assert_eq!(
        verdicts(&found),
        [("InvalidOperationException".to_owned(), Verdict::Unknown)]
    );
}

#[test]
fn a_write_inside_a_lambda_counts() {
    let text = "using System;\nstatic class Later { public static void Run(Action a) { } }\nclass C {\n    int count = 1;\n    void Set() { Later.Run(() => { count = 0; }); }\n    void M() { if (count == 0) throw new InvalidOperationException(); }\n}";
    let found = failability(text, "void M");
    assert_eq!(
        verdicts(&found),
        [("InvalidOperationException".to_owned(), Verdict::Possible)]
    );
}

#[test]
fn a_write_in_a_lambda_of_the_constructor_leaves_the_default() {
    let text = "using System;\nstatic class Later { public static void Run(Action a) { } }\nclass C {\n    bool closed;\n    C() { Later.Run(() => { closed = true; }); }\n    void M() { if (!closed) throw new InvalidOperationException(); }\n}";
    let found = failability(text, "void M");
    assert_eq!(
        verdicts(&found),
        [("InvalidOperationException".to_owned(), Verdict::Possible)]
    );
}

#[test]
fn a_library_property_is_not_a_field_of_the_project() {
    let text = "using System;\nclass C {\n    int M(Exception error) { var text = error.Message; return text.Length; }\n}";
    let found = failability(text, "int M");
    assert!(found.failures.is_empty(), "{found:?}");
}

#[test]
fn a_primary_constructor_parameter_has_what_its_callers_pass() {
    let text = "using System;\nclass Gate(int limit) {\n    public void Check() { if (limit < 0) throw new ArgumentException(); }\n}\nclass User { void Make() { new Gate(3).Check(); } }";
    let found = failability(text, "void Check");
    assert_eq!(
        verdicts(&found),
        [("ArgumentException".to_owned(), Verdict::Never)]
    );
}

#[test]
fn a_property_checked_against_null_before_the_call() {
    let text = "using System;\nclass C {\n    public Action Rerun { get; set; }\n    void Set() { Rerun = () => { }; }\n    void M() { if (Rerun != null) Rerun(); }\n}";
    let found = failability(text, "void M");
    assert!(found.failures.is_empty(), "{found:?}");
}

// MARK: - what the body writes to its inputs

/// The failability of `marker`'s member, compiled against the real framework;
/// `None` where none is installed.
fn failability_in_framework(text: &str, marker: &str) -> Option<Failability> {
    let semantic = compile(&[("C.cs", text)], true)?;
    let at = text.find(marker).expect("marker") + marker.len();
    semantic.failability(Path::new("/p/C.cs"), at as u32)
}

fn only(found: &Failability) -> Verdict {
    let [failure] = found.failures.as_slice() else {
        panic!("{found:?}")
    };
    failure.verdict
}

/// What the callers pass is what a parameter has on entry. Once the body
/// writes to it, the value is the body's: `b = 0` is not `b = 3`.
#[test]
fn a_parameter_assigned_in_the_body_is_not_what_the_callers_pass() {
    let text =
        "class C {\n    int X(int a, int b) { b = 0; return a / b; }\n    int Go() => X(1, 3);\n}";
    assert_eq!(only(&failability(text, "int X")), Verdict::Possible);
}

/// A write whose value is not followed (`-=`, `++`, a loop, `ref`) leaves the
/// parameter unknown from there on.
#[test]
fn a_parameter_changed_in_ways_not_followed_is_unknown() {
    let bodies = [
        "b -= 3; return a / b;",
        "for (int i = 0; i < 3; i++) b--; return a / b;",
        "while (b != 0) b--; return a / b;",
        "b = b - 3; return a / b;",
        "Reset(ref b); return a / b;",
        "Zero(out b); return a / b;",
    ];
    for body in bodies {
        let text = format!(
            "class C {{\n    static void Reset(ref int x) {{ x = 0; }}\n    static void Zero(out int x) {{ x = 0; }}\n    int X(int a, int b) {{ {body} }}\n    int Go() => X(1, 3);\n}}"
        );
        let found = failability(&text, "int X");
        assert_eq!(only(&found), Verdict::Unknown, "{body}");
    }
}

/// A lambda or a local function that writes the parameter does so whenever it
/// runs.
#[test]
fn a_parameter_written_by_a_closure_is_not_what_the_callers_pass() {
    let text = "using System;\nclass C {\n    int X(int a, int b) { Action f = () => { b = 0; }; f(); return a / b; }\n    int Y(int a, int b) { void Z() { b = 0; } Z(); return a / b; }\n    int Go() => X(1, 3) + Y(1, 3);\n}";
    assert_eq!(only(&failability(text, "int X")), Verdict::Possible);
    assert_eq!(only(&failability(text, "int Y")), Verdict::Possible);
}

/// A parameter set to null is null, whatever the callers pass.
#[test]
fn a_parameter_set_to_null_can_be_null() {
    let text = "class C {\n    int X(string s) { s = null; return s.Length; }\n    int Go() => X(\"x\");\n}";
    let found = failability(text, "int X");
    assert_eq!(
        verdicts(&found),
        [("NullReferenceException".to_owned(), Verdict::Possible)]
    );
}

/// A guard before the write says nothing of the value after it.
#[test]
fn a_guard_before_a_write_does_not_hold_after_it() {
    let text = "class C {\n    int X(int a, int b) { if (b == 0) return 0; b = b - b; return a / b; }\n    int Go() => X(1, 3);\n}";
    assert_eq!(only(&failability(text, "int X")), Verdict::Unknown);
}

/// A write further down a loop is there on the next round, however the
/// first went.
#[test]
fn a_write_further_down_a_loop_reaches_the_top_of_the_next_round() {
    let text = "class C {\n    int X(int a, int b) { int r = 0; if (b != 0) { for (int i = 0; i < 2; i++) { r += a / b; b = 0; } } return r; }\n    int Go() => X(1, 3);\n}";
    assert_ne!(only(&failability(text, "int X")), Verdict::Never);
}

/// What stays true: an unwritten parameter has what its callers pass, a guard
/// that nothing separates from the use applies, a write that cannot give zero
/// leaves no zero, and a local given zero is zero.
#[test]
fn what_is_true_stays_true() {
    let guarded = "class C {\n    int X(int a, int b) { if (b == 0) return 0; return a / b; }\n    int Go() => X(1, 3);\n}";
    assert_eq!(only(&failability(guarded, "int X")), Verdict::Never);
    let fixed = "class C {\n    int X(int a, int b) { if (b == 0) { b = 1; } return a / b; }\n    int Go() => X(1, 3) + X(2, 4);\n}";
    assert_eq!(only(&failability(fixed, "int X")), Verdict::Never);
    let zero = "class C {\n    int X(int a) { int z = 0; return a / z; }\n}";
    assert_eq!(only(&failability(zero, "int X")), Verdict::Always);
    let unwritten =
        "class C {\n    int X(int a, int b) { return a / b; }\n    int Go() => X(1, 0);\n}";
    assert_eq!(only(&failability(unwritten, "int X")), Verdict::Always);
}

/// A field a guard has looked at may be another by the time of the use: what
/// is called in between may write it.
#[test]
fn a_guard_on_a_field_does_not_survive_a_call() {
    let text = "class C {\n    int fld = 1;\n    void Mutate() { fld = 0; }\n    int X(int a) { if (fld != 0) { Mutate(); return a / fld; } return 0; }\n}";
    assert_eq!(only(&failability(text, "int X")), Verdict::Possible);
}

/// ... and a lock taken or released, and a `yield`.
#[test]
fn a_guard_on_a_field_does_not_survive_a_lock_or_a_yield() {
    let locked = "class C {\n    int fld = 1;\n    object o = new object();\n    void Zero() { fld = 0; }\n    int X(int a) { if (fld != 0) { lock (o) { return a / fld; } } return 0; }\n}";
    assert_eq!(only(&failability(locked, "int X")), Verdict::Possible);
    let yielded = "using System.Collections.Generic;\nclass C {\n    int fld = 1;\n    void Zero() { fld = 0; }\n    IEnumerable<int> X(int a) { if (fld != 0) { yield return 1; yield return a / fld; } }\n}";
    assert_eq!(
        only(&failability(yielded, "IEnumerable<int> X")),
        Verdict::Possible
    );
}

/// ... but not a `readonly` field, nor one that nothing in between touches,
/// nor a copy taken in a local.
#[test]
fn a_guard_on_a_field_survives_what_cannot_change_it() {
    let readonly = "class C {\n    readonly int ro = 2;\n    void Nothing() { }\n    int X(int a) { if (ro != 0) { Nothing(); return a / ro; } return 0; }\n}";
    assert_eq!(only(&failability(readonly, "int X")), Verdict::Never);
    let plain = "class C {\n    int fld = 1;\n    void Mutate() { fld = 0; }\n    int X(int a) { if (fld != 0) { return a / fld; } return 0; }\n}";
    assert_eq!(only(&failability(plain, "int X")), Verdict::Never);
    let copy = "class C {\n    int fld = 1;\n    void Mutate() { fld = 0; }\n    int X(int a) { var c = fld; if (c != 0) { Mutate(); return a / c; } return 0; }\n}";
    assert_eq!(only(&failability(copy, "int X")), Verdict::Never);
    let pure = "class C {\n    int fld = 1;\n    void Mutate() { fld = 0; }\n    int X(int a) { if (fld != 0) { var s = a.ToString(); return a / fld; } return 0; }\n}";
    assert_eq!(only(&failability(pure, "int X")), Verdict::Never);
}

/// A field of one object says nothing of the same field of another.
#[test]
fn a_guard_on_the_field_of_one_object_is_not_about_another() {
    let text = "class C {\n    public int n;\n    void Off() { n = 0; }\n    void On() { n = 1; }\n    int X(C o, C p) { if (o.n != 0) { return 1 / p.n; } return 0; }\n}";
    assert_eq!(only(&failability(text, "int X")), Verdict::Possible);
}

// MARK: - switches

/// The `default` of a switch holds where none of the other labels does.
#[test]
fn the_default_of_a_switch_is_none_of_the_other_labels() {
    let text = |calls: &str| {
        format!(
            "using System;\nclass C {{\n    int F(int x) {{ switch (x) {{ case 1: return 10; case 2: return 20; default: throw new InvalidOperationException(\"bad\"); }} }}\n    int Go() => {calls};\n}}"
        )
    };
    let never = failability(&text("F(1) + F(2)"), "int F");
    assert_eq!(only(&never), Verdict::Never);
    assert_eq!(never.failures[0].conditions[0].text, "x is not (1 or 2)");
    assert_eq!(only(&failability(&text("F(3)"), "int F")), Verdict::Always);
    assert_eq!(
        only(&failability(&text("F(1) + F(3)"), "int F")),
        Verdict::Possible
    );
}

/// So is the `_` arm of a switch expression, and a pattern arm holds where
/// its pattern matches and no arm before it did.
#[test]
fn the_arms_of_a_switch_expression_have_their_patterns_as_conditions() {
    let text = "using System;\nclass C {\n    int N(string s) => s switch { null => throw new ArgumentNullException(), _ => s.Length };\n    int K(int x) => x switch { 3 => throw new InvalidOperationException(), _ => 0 };\n    int W(int x) => x switch { > 5 => throw new InvalidOperationException(), _ => 0 };\n    int D(int x) => x switch { 1 => 1, _ => throw new InvalidOperationException() };\n    int Go() => N(\"a\") + K(1) + W(1) + D(1);\n}";
    for name in ["int N", "int K", "int W", "int D"] {
        assert_eq!(only(&failability(text, name)), Verdict::Never, "{name}");
    }
    let hit = "using System;\nclass C {\n    int N(string s) => s switch { null => throw new ArgumentNullException(), _ => 1 };\n    int W(int x) => x switch { > 5 => throw new InvalidOperationException(), _ => 0 };\n    int Go() => N(null) + W(9);\n}";
    assert_eq!(only(&failability(hit, "int N")), Verdict::Always);
    assert_eq!(only(&failability(hit, "int W")), Verdict::Always);
}

/// Several labels on a section, a `when`, and a jump into a section are
/// conditions too.
#[test]
fn labels_with_guards_and_jumps_are_conditions() {
    let several = "using System;\nclass C {\n    int F(int x) { switch (x) { case 1: case 2: throw new Exception(); default: return 0; } }\n    int Go() => F(3);\n}";
    assert_eq!(only(&failability(several, "int F")), Verdict::Never);
    let guard = "using System;\nclass C {\n    int F(int x) { switch (x) { case int n when n > 5: throw new Exception(); default: return 0; } }\n    int Go() => F(1);\n}";
    assert_ne!(only(&failability(guard, "int F")), Verdict::Always);
    let jump = "using System;\nclass C {\n    int F(int x) { switch (x) { case 1: goto case 2; case 2: throw new Exception(); default: return 0; } }\n    int Go() => F(1);\n}";
    assert_ne!(only(&failability(jump, "int F")), Verdict::Never);
}

/// What follows a switch whose sections return is reached only by the values
/// they did not take.
#[test]
fn a_throw_after_a_switch_that_returns_is_not_certain() {
    let text = "using System;\nclass C {\n    int F(int x) { switch (x) { case 1: return 1; } throw new Exception(); }\n    int Go() => F(1);\n}";
    assert_ne!(only(&failability(text, "int F")), Verdict::Always);
}

// MARK: - virtual calls

const VIRTUAL: &str = "using System;\nclass Base { public virtual int Get(int i) => throw new IndexOutOfRangeException(); public int Plain(int i) => throw new IndexOutOfRangeException(); }\nclass Derived : Base { public override int Get(int i) => i; }\n";

/// A call that goes through the run-time type runs a body the call does not
/// show: what the base's does is at most possible.
#[test]
fn a_virtual_call_does_not_run_the_base_body_for_certain() {
    let text = format!(
        "{VIRTUAL}class Use {{ int Go() {{ Base b = new Derived(); return b.Get(0); }} int Go2(Base b) => b.Get(0); }}"
    );
    for name in ["int Go()", "int Go2"] {
        let found = failability(&text, name);
        assert_eq!(only(&found), Verdict::Unknown, "{name}");
    }
}

/// Where the type is certain, or the call is not virtual, the body is the one
/// that runs.
#[test]
fn a_call_to_a_body_that_must_run_still_fails_always() {
    let text = format!(
        "{VIRTUAL}class Use {{ int A() => new Base().Get(0); int B() {{ Derived d = new Derived(); return d.Plain(0); }} }}"
    );
    for name in ["int A", "int B"] {
        assert_eq!(only(&failability(&text, name)), Verdict::Always, "{name}");
    }
    let sealed = "using System;\nsealed class S { public virtual int Get(int i) => throw new IndexOutOfRangeException(); }\nclass Use { int Go(S s) => s.Get(0); }";
    assert_eq!(only(&failability(sealed, "int Go")), Verdict::Always);
    let based = "using System;\nclass Base { public virtual int Get(int i) => throw new IndexOutOfRangeException(); }\nclass Mid : Base { public override int Get(int i) => base.Get(i); }";
    assert_eq!(only(&failability(based, "int Get")), Verdict::Always);
}

// MARK: - what a catch lets through, what a call does not run

const THROWER: &str = "using System;\nstatic class H { public static void Thrower() { throw new InvalidOperationException(\"x\"); } }\n";

/// A `catch` with a filter takes the failure only where the filter holds:
/// where that is not known, the failure is possible and not certain.
#[test]
fn a_filtered_catch_makes_the_failure_possible() {
    let text = format!(
        "{THROWER}class C {{\n    void A() {{ try {{ H.Thrower(); }} catch (InvalidOperationException e) when (e.Message == \"x\") {{ }} }}\n    void B(bool c) {{ try {{ H.Thrower(); }} catch (InvalidOperationException) when (c) {{ }} }}\n}}"
    );
    assert_eq!(only(&failability(&text, "void A")), Verdict::Possible);
    assert_eq!(only(&failability(&text, "void B")), Verdict::Possible);
}

/// A filter that is true takes it; one that is false lets it through.
#[test]
fn a_filter_that_is_known_decides() {
    let text = format!(
        "{THROWER}class C {{\n    void A() {{ try {{ H.Thrower(); }} catch (InvalidOperationException) when (true) {{ }} }}\n    void B() {{ try {{ H.Thrower(); }} catch (InvalidOperationException) when (false) {{ }} }}\n    void D() {{ try {{ H.Thrower(); }} catch (InvalidOperationException) {{ }} }}\n}}"
    );
    assert!(failability(&text, "void A").failures.is_empty());
    assert_eq!(only(&failability(&text, "void B")), Verdict::Always);
    assert!(failability(&text, "void D").failures.is_empty());
}

/// A call of an `async` method that is not awaited does not throw: the
/// failure is in the task it gives back. An awaited one does.
#[test]
fn an_async_call_that_is_not_awaited_does_not_throw() {
    let text = "using System;\nusing System.Threading.Tasks;\nstatic class H {\n    public static async Task As() { throw new Exception(\"boom\"); }\n    public static Task Sync() { throw new Exception(\"sync\"); }\n}\nclass C {\n    void A() { H.As(); }\n    async Task B() { await H.As(); }\n    void D() { H.Sync(); }\n    void E() { var t = H.As(); }\n}";
    let Some(a) = failability_in_framework(text, "void A") else {
        return;
    };
    assert!(a.failures.is_empty(), "{a:?}");
    let b = failability_in_framework(text, "Task B").expect("framework");
    assert_eq!(only(&b), Verdict::Always);
    let d = failability_in_framework(text, "void D").expect("framework");
    assert_eq!(only(&d), Verdict::Always);
    let e = failability_in_framework(text, "void E").expect("framework");
    assert!(e.failures.is_empty(), "{e:?}");
}

/// A call of an iterator runs none of its body until it is enumerated.
#[test]
fn an_iterator_call_does_not_run_the_body() {
    let text = "using System;\nusing System.Collections.Generic;\nstatic class H {\n    public static IEnumerable<int> It() { throw new Exception(\"it\"); yield return 1; }\n}\nclass C {\n    void A() { var x = H.It(); }\n}";
    let Some(a) = failability_in_framework(text, "void A") else {
        return;
    };
    assert!(a.failures.is_empty(), "{a:?}");
}

/// What a `catch` does runs only when the block before it fails; a loop's
/// body only when it has something to walk; what follows a loop that may
/// return only when it did not.
#[test]
fn code_that_may_not_run_is_not_certain() {
    let text = "using System;\nclass C {\n    int A() { int x = 0; try { x = 1; } catch (Exception) { throw new Exception(\"never\"); } return x; }\n    int B(int[] xs) { foreach (var x in xs) { throw new Exception(\"first\"); } return 0; }\n    int D(int[] xs) { foreach (var x in xs) { if (x > 1) return x; } throw new Exception(\"none\"); }\n    int E(int a, int b) { if (a > 0) { if (b > 0) return 1; } throw new Exception(\"rest\"); }\n}";
    for name in ["int A", "int B", "int D", "int E"] {
        assert_ne!(only(&failability(text, name)), Verdict::Always, "{name}");
    }
}

/// A check of the count before `First()` makes it safe.
#[test]
fn first_after_a_count_check() {
    let text = "using System.Collections.Generic;\nusing System.Linq;\nnamespace System.Linq { public static class Enumerable { public static extern T First<T>(this IEnumerable<T> source); public static extern bool Any<T>(this IEnumerable<T> source); } }\nclass C {\n    List<int> items = new List<int>();\n    int A() { return items.Count > 0 ? items.First() : 0; }\n    int B() { if (items.Count == 0) return 0; return items.First(); }\n    int D() { return items.Count >= 0 ? items.First() : 0; }\n}";
    assert!(failability(text, "int A").failures.is_empty());
    assert!(failability(text, "int B").failures.is_empty());
    assert_eq!(failability(text, "int D").failures.len(), 1);
}

// MARK: - what else a call or a value hides

/// A local function's own body is what a call of it runs.
#[test]
fn a_local_function_is_followed_into_its_own_body() {
    let text = "using System;\nclass C {\n    int Y(int a) { void Z() { throw new Exception(\"z\"); } Z(); return a; }\n}";
    let found = failability(text, "int Y");
    let [failure] = found.failures.as_slice() else {
        panic!("{found:?}")
    };
    assert_eq!(failure.verdict, Verdict::Always);
    assert_eq!(failure.chain[0].callee, "C.Y.Z");
    assert_eq!(failure.message.as_deref(), Some("z"));
}

/// A method that implements an interface member is called through the
/// interface by calls that do not name it: what the calls that do name it
/// pass is not all it gets.
#[test]
fn an_implementation_of_an_interface_member_does_not_trust_its_callers() {
    let text = "interface IDiv { int Div(int b); }\nclass Impl : IDiv {\n    public int Div(int b) { return 10 / b; }\n}\nclass Use { int Go(Impl i) => i.Div(3); int Via(IDiv d) => d.Div(0); }";
    let found = failability(text, "public int Div");
    assert_eq!(only(&found), Verdict::Unknown);
    assert_eq!(found.failures[0].inputs[0].origin, Origin::Escapes);
}

/// A value the type cannot hold is not the value it has: `(byte)256` is `0`.
#[test]
fn a_value_that_wraps_is_not_known() {
    let text =
        "class C {\n    int X(int a, int b) { return a / (byte)b; }\n    int Go() => X(1, 256);\n}";
    assert_ne!(only(&failability(text, "int X")), Verdict::Never);
}

/// `x ??= y` evaluates `y` only where `x` is null.
#[test]
fn a_coalesce_assignment_runs_its_value_only_for_null() {
    let text = "using System;\nclass C {\n    string Make() => throw new Exception(\"make\");\n    int X(string s) { s ??= Make(); return 1; }\n    int Go() => X(\"a\");\n}";
    assert_eq!(only(&failability(text, "int X")), Verdict::Never);
}

/// A property an interface declares, or a class lets a subtype override, is
/// not a field: nothing writing to it here says what it gives.
#[test]
fn an_interface_or_virtual_property_is_not_a_field_nothing_writes() {
    let text = "interface IMap { string Name { get; } }\nclass A : IMap { public string Name { get; } = \"a\"; }\nclass B { public virtual string Title { get; } }\nclass C {\n    int X(IMap m) { return m.Name.Length; }\n    int Y(B b) { return b.Title.Length; }\n}";
    assert!(failability(text, "int X").failures.is_empty());
    assert!(failability(text, "int Y").failures.is_empty());
}

/// What follows a label is reached by the `goto`s that name it, which come
/// with conditions of their own: it is not reached for certain.
#[test]
fn code_after_a_label_is_reached_by_a_jump_not_for_certain() {
    let text = "using System;\nclass C {\n    int F(int a) { if (a > 3) goto Found; return 0; Found: throw new Exception(\"found\"); }\n}";
    let found = failability(text, "int F");
    let [failure] = found.failures.as_slice() else {
        panic!("{found:?}")
    };
    assert_eq!(failure.verdict, Verdict::Possible);
    assert_eq!(
        failure.conditions[0].text,
        "a jump or the code above reaches this label"
    );
}
