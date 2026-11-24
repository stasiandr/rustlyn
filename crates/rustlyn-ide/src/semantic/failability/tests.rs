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
