//! Tests of completion, one group per provider. Each source marks the
//! cursor with `$$`.

use std::path::Path;

use super::super::tests::compile;
use super::*;

/// The completions at `$$` in a file compiled with `others` beside it.
fn complete_with(others: &[(&str, &str)], source: &str) -> (Completions, String) {
    let offset = source
        .find("$$")
        .expect("the source should mark the cursor") as u32;
    let text = source.replacen("$$", "", 1);
    let mut files: Vec<(&str, &str)> = others.to_vec();
    files.push(("Main.cs", &text));
    let semantic = compile(&files, false).expect("compiled");
    let list = semantic
        .completions(Path::new("/p/Main.cs"), offset, None)
        .expect("completed");
    (list, text)
}

fn complete(source: &str) -> Completions {
    complete_with(&[], source).0
}

fn labels(list: &Completions) -> Vec<&str> {
    list.items.iter().map(|item| item.label.as_str()).collect()
}

fn keywords(list: &Completions) -> Vec<&str> {
    list.items
        .iter()
        .filter(|item| item.kind == CompletionKind::Keyword)
        .map(|item| item.label.as_str())
        .collect()
}

fn item<'a>(list: &'a Completions, label: &str) -> &'a Completion {
    list.items
        .iter()
        .find(|item| item.label == label)
        .unwrap_or_else(|| panic!("{label} in {:?}", labels(list)))
}

#[track_caller]
fn has_all(found: &[&str], wanted: &[&str]) {
    for word in wanted {
        assert!(found.contains(word), "{word} should be in {found:?}");
    }
}

#[track_caller]
fn has_none(found: &[&str], unwanted: &[&str]) {
    for word in unwanted {
        assert!(!found.contains(word), "{word} should not be in {found:?}");
    }
}

// MARK: - keywords

#[test]
fn a_statement_starts_with_statement_keywords_and_no_modifiers() {
    let list = complete("class C { void M() { int a = 1; $$ } }");
    let words = keywords(&list);
    has_all(
        &words,
        &[
            "if", "for", "foreach", "var", "return", "while", "new", "this", "int",
        ],
    );
    has_none(
        &words,
        &[
            "public",
            "override",
            "get",
            "await",
            "break",
            "case",
            "namespace",
            "in",
        ],
    );
    // Symbols too: the local, the method.
    has_all(&labels(&list), &["a", "M", "C"]);
}

#[test]
fn await_is_offered_only_in_an_async_body() {
    let plain = complete("class C { void M() { $$ } }");
    assert!(!keywords(&plain).contains(&"await"));
    let with_async = complete("class C { async void M() { $$ } }");
    assert!(keywords(&with_async).contains(&"await"));
    let lambda = complete("class C { void M() { System.Action a = async () => { $$ }; } }");
    assert!(keywords(&lambda).contains(&"await"));
}

#[test]
fn loops_offer_break_and_continue_and_a_switch_its_labels() {
    let in_loop = complete("class C { void M() { while (true) { $$ } } }");
    has_all(&keywords(&in_loop), &["break", "continue"]);
    let in_switch = complete("class C { void M(int x) { switch (x) { $$ } } }");
    assert_eq!(keywords(&in_switch), vec!["case", "default"]);
    let in_section = complete("class C { void M(int x) { switch (x) { case 1: $$ } } }");
    has_all(
        &keywords(&in_section),
        &["break", "case", "default", "return"],
    );
    has_none(&keywords(&in_section), &["continue"]);
}

#[test]
fn else_follows_an_if_and_catch_follows_a_try() {
    let after_if = complete("class C { void M(bool b) { if (b) { } $$ } }");
    assert!(keywords(&after_if).contains(&"else"));
    let after_try = complete("class C { void M() { try { } $$ } }");
    has_all(&keywords(&after_try), &["catch", "finally"]);
    let embedded = complete("class C { void M(bool b) { if (b) $$ } }");
    has_none(&keywords(&embedded), &["else"]);
    has_all(&keywords(&embedded), &["return", "if"]);
    let plain = complete("class C { void M() { M(); $$ } }");
    has_none(&keywords(&plain), &["else", "catch"]);
}

#[test]
fn a_class_body_offers_modifiers_and_types_but_no_statements() {
    let list = complete("class C { int x; $$ }");
    let words = keywords(&list);
    has_all(
        &words,
        &[
            "public", "private", "override", "static", "void", "class", "int", "event",
        ],
    );
    has_none(&words, &["if", "return", "var", "this", "namespace", "get"]);
    // No members or locals: only what a declaration can start with.
    has_none(&labels(&list), &["x"]);
    has_all(&labels(&list), &["C"]);
}

#[test]
fn modifiers_already_written_are_not_offered_again() {
    let list = complete("class C { public static $$ }");
    let words = keywords(&list);
    has_all(&words, &["void", "readonly", "int", "class"]);
    has_none(
        &words,
        &[
            "public", "static", "private", "virtual", "override", "abstract",
        ],
    );
    let protected = complete("class C { protected $$ }");
    has_all(&keywords(&protected), &["internal", "virtual"]);
    has_none(&keywords(&protected), &["public", "protected"]);
}

#[test]
fn a_namespace_offers_type_declarations() {
    let list = complete("namespace N { $$ }");
    let words = keywords(&list);
    has_all(
        &words,
        &[
            "class",
            "public",
            "interface",
            "enum",
            "namespace",
            "record",
        ],
    );
    has_none(&words, &["if", "void", "override", "return"]);
    let top = complete("using System;\n$$");
    has_all(
        &keywords(&top),
        &["class", "using", "namespace", "if", "var"],
    );
}

#[test]
fn an_expression_offers_expression_keywords() {
    let list = complete("class C { void M() { var x = $$ } }");
    let words = keywords(&list);
    has_all(
        &words,
        &[
            "new", "this", "true", "false", "null", "typeof", "nameof", "default",
        ],
    );
    has_none(&words, &["if", "public", "return", "class", "void", "var"]);
}

#[test]
fn a_static_member_has_no_this_and_no_instance_members() {
    let list =
        complete("class C { int count; static int total; void Go() { } static void M() { $$ } }");
    has_none(&labels(&list), &["this", "base", "count", "Go"]);
    has_all(&labels(&list), &["total", "M"]);
}

#[test]
fn nothing_follows_a_dot_but_members() {
    let list = complete("class C { int Hp; void M(C c) { c.$$ } }");
    assert!(keywords(&list).is_empty(), "{:?}", keywords(&list));
    assert!(labels(&list).contains(&"Hp"));
}

#[test]
fn a_generic_declaration_is_followed_by_where() {
    let list = complete("class G<T> $$ { }");
    assert_eq!(keywords(&list), vec!["where"]);
    let constraint = complete("class G<T> where T : $$ { }");
    has_all(
        &keywords(&constraint),
        &["class", "struct", "new", "unmanaged", "notnull"],
    );
}

#[test]
fn foreach_wants_in_after_its_variable() {
    let list = complete("class C { void M(int[] xs) { foreach (var x $$ } }");
    assert_eq!(keywords(&list), vec!["in"]);
}

#[test]
fn accessor_lists_offer_the_accessors_not_yet_written() {
    let empty = complete("class C { int P { $$ } }");
    has_all(&keywords(&empty), &["get", "set", "init"]);
    has_none(&keywords(&empty), &["if", "public", "class"]);
    let after_get = complete("class C { int P { get; $$ } }");
    has_all(&keywords(&after_get), &["set", "init"]);
    has_none(&keywords(&after_get), &["get"]);
}

#[test]
fn comments_and_strings_offer_nothing() {
    assert!(
        complete("class C { void M() { // hel$$\n } }")
            .items
            .is_empty()
    );
    assert!(
        complete("class C { void M() { var s = \"hel$$\"; } }")
            .items
            .is_empty()
    );
    assert!(complete("class C { /* a $$ */ }").items.is_empty());
}

// MARK: - symbols by place

#[test]
fn after_new_only_types_and_the_expected_one_preselected() {
    let (list, _) = complete_with(
        &[],
        "using System.Collections.Generic;\n\
         class C { int field; void M(int local) { List<int> xs = new $$ } }",
    );
    let found = labels(&list);
    has_none(&found, &["local", "field", "M", "if", "this"]);
    has_all(&found, &["C", "List<int>"]);
    let preselected = item(&list, "List<int>");
    assert!(preselected.preselect);
    assert_eq!(preselected.insert_text.as_deref(), Some("List<int>"));
    assert_eq!(preselected.filter_text.as_deref(), Some("List"));

    let plain = complete("class P { } class C { void M() { P p = new $$ } }");
    assert!(item(&plain, "P").preselect);
}

#[test]
fn where_an_enum_is_expected_its_members_are_offered_first() {
    let source = "enum Color { Red, Green }\n\
                  class C { void M(Color given) { Color c = $$ } }";
    let list = complete(source);
    let red = item(&list, "Color.Red");
    assert!(red.preselect);
    assert_eq!(red.kind, CompletionKind::EnumMember);
    let first = list
        .items
        .iter()
        .find(|item| item.preselect)
        .expect("preselected");
    assert_eq!(first.label, "Color.Green");

    let compared = complete("enum Color { Red }\nclass C { bool M(Color c) { return c == $$ } }");
    assert!(item(&compared, "Color.Red").preselect);

    let case = complete(
        "enum Color { Red, Blue }\nclass C { void M(Color c) { switch (c) { case $$ } } }",
    );
    assert!(item(&case, "Color.Blue").preselect);

    let returned = complete("enum Color { Red }\nclass C { Color M() { return $$ } }");
    assert!(item(&returned, "Color.Red").preselect);

    let argument =
        complete("enum Color { Red }\nclass C { void Paint(Color c) { } void M() { Paint($$ } }");
    assert!(item(&argument, "Color.Red").preselect);
}

#[test]
fn type_only_places_offer_types_and_namespaces() {
    let sources = [
        "class C { int field; void M() { var t = typeof($$ } }",
        "class B { } class C : $$ { int field; }",
        "class C { int field; void M(object o) { var x = o as $$ } }",
        "class C { int field; void M($$) { } }",
        "using System.Collections.Generic;\nclass C { int field; void M() { var x = new List<$$ } }",
    ];
    for source in sources {
        let list = complete(source);
        let found = labels(&list);
        assert!(found.contains(&"C"), "{source}: {found:?}");
        assert!(!found.contains(&"field"), "{source}: {found:?}");
        assert!(!found.contains(&"M"), "{source}: {found:?}");
    }
    let parameter = complete("class C { void M($$) { } }");
    has_all(&keywords(&parameter), &["ref", "out", "params", "int"]);
}

#[test]
fn this_and_base_offer_the_members_of_the_type() {
    let source = "class B { protected int Shared; private int hidden; public virtual void Go() { } }\n\
                  class C : B { int own; void M() { base.$$ } }";
    let list = complete(source);
    has_all(&labels(&list), &["Shared", "Go"]);
    has_none(&labels(&list), &["hidden", "own"]);
    let this = complete("class C { int own; void M() { this.$$ } }");
    has_all(&labels(&this), &["own", "M"]);
}

/// A value's members are its type's as constructed: no type parameters
/// among them, the receiver's type arguments in their signatures, and
/// nothing `protected` the code cannot reach through that value.
#[test]
fn a_constructed_receiver_offers_its_members_as_it_has_them() {
    let source = "class Pair<TKey, TValue> { public TKey Key; public TValue Value; protected void Swap() { } }\n\
                  class Named : Pair<string, int> { }\n\
                  class Item { }\n\
                  static class Ext { public static T Left<T>(this Pair<T, Item> pair) => pair.Key; }\n\
                  class C { void M(Pair<string, Item> p, Named n) { p.$$ } }";
    let list = complete(source);
    let found = labels(&list);
    has_all(&found, &["Key", "Value", "Left"]);
    has_none(&found, &["TKey", "TValue", "Swap"]);
    assert_eq!(item(&list, "Key").detail, "string Key");
    assert_eq!(item(&list, "Value").detail, "Item Value");
    assert_eq!(
        item(&list, "Left").detail,
        "string Left<string>(this Pair<string, Item> pair)"
    );
    // Through a base type that names the arguments.
    let derived = complete(&source.replace("p.$$", "n.$$"));
    assert_eq!(item(&derived, "Value").detail, "int Value");
}

/// What every value has, a class that names no base included: `object`'s
/// members.
#[test]
fn a_class_that_names_no_base_still_has_what_object_has() {
    let list = complete("class P { public int Hp; }\nclass C { void M(P p) { p.$$ } }");
    has_all(
        &labels(&list),
        &["Hp", "ToString", "Equals", "GetHashCode", "GetType"],
    );
}

/// A type parameter has what its constraints promise, and what every value
/// has.
#[test]
fn a_type_parameter_offers_what_its_constraints_promise() {
    let source = "interface IShape { double Area { get; } }\n\
                  class Shape { public int Sides; }\n\
                  class C { void M<T, U>(T item, U other) where T : Shape, IShape where U : T { item.$$ } }";
    let list = complete(source);
    has_all(&labels(&list), &["Area", "Sides", "ToString"]);
    // Constrained by another type parameter: by what that one is.
    let other = complete(&source.replace("item.$$", "other.$$"));
    has_all(&labels(&other), &["Area", "Sides"]);
}

/// `p.Name.Length` with `Name` deleted reads `p..Length`, a range to the
/// lexer; the cursor between the dots still asks for a member of `p`.
#[test]
fn a_name_deleted_from_between_two_dots_is_a_member_still() {
    let list =
        complete("class P { public string Name; }\nclass C { void M(P p) { var n = p.$$.Name; } }");
    has_all(&labels(&list), &["Name", "ToString"]);
    // `!p..Done` is the range from `!p`: the member is still `p`'s.
    let negated =
        complete("class P { public bool Done; }\nclass C { void M(P p) { var n = !p.$$.Done; } }");
    has_all(&labels(&negated), &["Done"]);
}

// MARK: - lambdas

/// A source for the lambda tests: `Map` is `Select`, whose result type only
/// the lambda's body can say.
const MAP: &str = "using System;\nusing System.Collections.Generic;\n\
                   static class Seq {\n\
                       public static IEnumerable<R> Map<T, R>(this IEnumerable<T> source, Func<T, R> f) => null;\n\
                       public static IEnumerable<R> Map<T, R>(this IEnumerable<T> source, Func<T, int, R> f) => null;\n\
                   }\n\
                   class P { public int Age; public string Name; }\n";

/// `list.Map(e => e.)`: the body says nothing about `R` yet, so `Map`
/// cannot be called — and `e` is an element of the list all the same,
/// as inference had it when it asked the lambda what it returns.
#[test]
fn a_lambda_whose_call_cannot_be_settled_yet_knows_its_parameter() {
    let typing = complete(&format!(
        "{MAP}class C {{ void M(List<P> list) {{ var r = list.Map(e => e.$$); }} }}"
    ));
    has_all(&labels(&typing), &["Age", "Name"]);
    // Cut off where it is being typed, with the rest of the file after.
    let cut = complete(&format!(
        "{MAP}class C {{ void M(List<P> list) {{ var r = list.Map(e => e.$$\n    }}\n}}"
    ));
    has_all(&labels(&cut), &["Age", "Name"]);
    // And the other overload, by how many parameters the lambda has.
    let indexed = complete(&format!(
        "{MAP}class C {{ void M(List<P> list) {{ var r = list.Map((e, i) => e.$$); }} }}"
    ));
    has_all(&labels(&indexed), &["Age", "Name"]);
}

/// A lambda handed to a call missing an argument still knows what the call
/// would hand it: the delegate the candidate takes in its place.
#[test]
fn a_lambda_short_of_the_arguments_after_it_knows_its_parameters() {
    let source = "using System;\nclass Context { public int Instance; }\n\
                  class Factory { public Factory(Func<Context, int, string> make, string[] sets) { } }\n\
                  class C { void M() { var f = new Factory((context, _) => context.$$); } }";
    has_all(&labels(&complete(source)), &["Instance"]);
}

/// What a call that does not resolve yet is given and nothing gave a type —
/// a `new(…)`, a collection expression — is still bound inside, lambdas
/// and all.
#[test]
fn a_lambda_inside_what_a_call_half_typed_is_given_knows_its_parameter() {
    let list = complete(&format!(
        "{MAP}class Key {{ public Key(int id, P[] people) {{ }} }}\n\
         class Cache {{ public void Add(Key key, int value) {{ }} }}\n\
         class C {{ void M(Cache cache, List<P> people) {{ cache.Add(new(1, [.. people.Map(p => p.$$\n    }}\n}}"
    ));
    has_all(&labels(&list), &["Age", "Name"]);
}

/// A type parameter of the code's own is a type like any other, and no
/// lambda becomes one: with `Split`'s `T` inferred from `source` as the
/// caller's `TSource`, `Split(source, separator)` is not what `item =>` is
/// given to.
#[test]
fn a_lambda_does_not_become_a_type_parameter_of_the_code_around_it() {
    let list = complete(
        "using System;\nusing System.Collections.Generic;\n\
         static class Seq {\n\
             public static IEnumerable<T[]> Split<T>(this IEnumerable<T> source, T separator) => null;\n\
             public static IEnumerable<T[]> Split<T>(this IEnumerable<T> source, Func<T, bool> separator) => null;\n\
         }\n\
         class P { public int Age; }\n\
         static class C {\n\
             static IEnumerable<TSource[]> M<TSource>(IEnumerable<TSource> source) where TSource : P {\n\
                 return Seq.Split(source, item => item.$$\n\
             }\n\
         }",
    );
    has_all(&labels(&list), &["Age"]);
}

/// A lambda given ahead of the argument that says what one of its
/// parameters is — `state`, by the argument after it — still knows the
/// others.
#[test]
fn a_lambda_ahead_of_what_types_one_parameter_knows_the_others() {
    let source = "using System;\nclass Context { public int Id; }\n\
                  static class Pipeline {\n\
                      public static int Execute<TState>(Func<Context, TState, int> callback, TState state) => 0;\n\
                  }\n\
                  class C { void M() { Pipeline.Execute(static (context, state) => context.$$); } }";
    has_all(&labels(&complete(source)), &["Id"]);
}

/// Type arguments written pick the candidates with as many: `Find<Image>`
/// is not `Find<T, U>`, whatever a lambda would be handed there.
#[test]
fn type_arguments_written_say_which_candidate_types_a_lambda() {
    let source = "using System;\nclass Image { public int Width; }\n\
                  class C {\n\
                      static T Find<T, U>(Func<string, bool> match, int depth) => default;\n\
                      static T Find<T>(Func<T, bool> match, int depth) => default;\n\
                      void M() { var found = Find<Image>(image => image.$$); }\n\
                  }";
    has_all(&labels(&complete(source)), &["Width"]);
}

/// An extension method is looked for in each namespace out from the code,
/// and a lambda keeps what the nearest ones said of it: LINQ's `Select`s
/// further out, one of whose delegates takes `(x, index, cancellation)`,
/// know less of `x` than the stream's own.
#[test]
fn a_lambda_keeps_what_the_nearest_extension_methods_said_of_it() {
    let source = "using System;\nusing System.Linq;\n\
                  namespace Rx {\n\
                      class Note { public int Kind; }\n\
                      static class Stream {\n\
                          public static IObservable<R> Select<T, R>(this IObservable<T> source, Func<T, R> f) => null;\n\
                          public static IObservable<R> Select<T, R>(this IObservable<T> source, Func<T, int, R> f) => null;\n\
                      }\n\
                      namespace Tests {\n\
                          class C { void M(IObservable<Note> notes) { notes.Select(x => x.$$\n    }\n}\n\
                      }\n\
                  }";
    let offset = source.find("$$").expect("a cursor") as u32;
    let text = source.replacen("$$", "", 1);
    let Some(semantic) = compile(&[("Main.cs", &text)], true) else {
        return;
    };
    let list = semantic
        .completions(Path::new("/p/Main.cs"), offset, None)
        .expect("completed");
    has_all(&labels(&list), &["Kind"]);
}

/// `p.Ag` with the next line read into it — `p.Ag other = 1;`, a
/// declaration to the parser and `p.Ag` the name of its type — is still a
/// member of `p` being typed; so is `e.Ag (a, b) => 1`, to the parser a
/// lambda that writes its return type.
#[test]
fn a_member_typed_above_the_next_line_is_still_a_member() {
    let list = complete(
        "class P { public int Age; }\nclass C { void M(P p) { int other; p.Ag$$\n other = 1; } }",
    );
    has_all(&labels(&list), &["Age"]);
    let lambda = complete(
        "using System;\nclass P { public int Age; }\n\
         class C { void M(Func<P, int> f) { f = e => Run(e.Ag$$\n (a, b) => 1); } static int Run(int x) => x; }",
    );
    has_all(&labels(&lambda), &["Age"]);
    // A namespace is a name of types still.
    let named = complete("class C { void M() { System.Coll$$\n int other = 1; } }");
    has_all(&labels(&named), &["Collections"]);
}

#[test]
fn a_conditional_access_offers_members() {
    let list = complete("class P { public int Hp; }\nclass C { void M(P p) { var x = p?.$$ } }");
    assert!(labels(&list).contains(&"Hp"));
}

#[test]
fn attributes_are_offered_without_their_suffix() {
    let source = "class MarkerAttribute : System.Attribute { }\nclass Plain { }\n\
                  [$$]\nclass C { }";
    let list = complete(source);
    let marker = item(&list, "Marker");
    assert_eq!(marker.kind, CompletionKind::Class);
    has_none(&labels(&list), &["Plain", "C", "class", "MarkerAttribute"]);
    assert!(labels(&list).contains(&"System"));
}

#[test]
fn using_offers_namespaces_and_using_static_types() {
    let others = [(
        "L.cs",
        "namespace Lib.Tools { public static class Kit { } }",
    )];
    let (plain, _) = complete_with(&others, "using $$");
    has_all(&labels(&plain), &["Lib", "System", "static"]);
    has_none(&labels(&plain), &["if", "class"]);
    let (nested, _) = complete_with(&others, "using Lib.$$");
    assert_eq!(labels(&nested), vec!["Tools"]);
    let (types, _) = complete_with(&others, "using static Lib.Tools.$$");
    assert_eq!(labels(&types), vec!["Kit"]);
}

// MARK: - override and partial

#[test]
fn override_lists_what_the_bases_let_be_overridden() {
    let source = "class B { public virtual int Twice(int a) => a * 2; public abstract void Run(); \
                  public virtual string Name { get; set; } public void Plain() { } \
                  protected virtual void Hook(ref int x, out string y) { y = null; } }\n\
                  class C : B {\n    public override string ToString() => \"\";\n    override $$\n}";
    let (list, text) = complete_with(&[], source);
    let found = labels(&list);
    has_all(
        &found,
        &[
            "Twice(int)",
            "Run()",
            "Name",
            "Hook(int, string)",
            "Equals(object)",
            "GetHashCode()",
        ],
    );
    has_none(&found, &["Plain()", "ToString()", "if", "class"]);

    let twice = item(&list, "Twice(int)");
    assert_eq!(twice.filter_text.as_deref(), Some("Twice"));
    assert_eq!(
        twice.insert_text.as_deref(),
        Some("public override int Twice(int a)\n    {\n        return base.Twice(a);\n    }")
    );
    // The `override` written so far is replaced.
    let first = text
        .find("override $$")
        .unwrap_or_else(|| text.find("override ").expect("typed")) as u32;
    let written = text.rfind("override ").expect("typed") as u32;
    assert_eq!(twice.additional_edits.len(), 1);
    assert_eq!(twice.additional_edits[0].span.start(), written.max(first));
    assert_eq!(twice.additional_edits[0].text, "");

    let run = item(&list, "Run()");
    assert!(
        run.insert_text
            .as_deref()
            .is_some_and(|text| text.contains("NotImplementedException"))
    );
    let hook = item(&list, "Hook(int, string)");
    assert!(
        hook.insert_text.as_deref().is_some_and(|text| text
            .starts_with("protected override void Hook(ref int x, out string y)")
            && text.contains("base.Hook(ref x, out y);")),
        "{:?}",
        hook.insert_text
    );
    let name = item(&list, "Name");
    assert!(name.insert_text.as_deref().is_some_and(
        |text| text.contains("get => base.Name;") && text.contains("set => base.Name = value;")
    ));
    let caret = twice.caret.expect("a caret") as usize;
    assert!(twice.text_to_insert()[caret..].starts_with("return base.Twice"));
}

#[test]
fn a_sealed_override_ends_the_line() {
    let source = "class A { public virtual void Go() { } }\n\
                  class B : A { public sealed override void Go() { } }\n\
                  class C : B { override $$ }";
    let list = complete(source);
    has_none(&labels(&list), &["Go()"]);
    let protected = complete(
        "abstract class B { protected abstract void Run(); }\nclass C : B { protected override $$ }",
    );
    assert_eq!(labels(&protected), vec!["Run()"]);
}

#[test]
fn partial_offers_the_partial_methods_not_yet_implemented() {
    let others = [(
        "Part.cs",
        "partial class C { partial void OnLoaded(int count); partial void Done(); }",
    )];
    let (list, _) = complete_with(
        &others,
        "partial class C {\n    partial void Done() { }\n    partial $$\n}",
    );
    let found = labels(&list);
    has_all(&found, &["OnLoaded(int count)", "void"]);
    has_none(&found, &["Done()"]);
    let item = item(&list, "OnLoaded(int count)");
    assert_eq!(
        item.insert_text.as_deref(),
        Some("partial void OnLoaded(int count)\n    {\n        \n    }")
    );
}

// MARK: - named arguments

#[test]
fn named_arguments_are_offered_for_the_parameters_not_yet_named() {
    let source = "class C { void Draw(int width, int height, bool fill = false) { } \
                  void Draw(string label) { } \
                  void M() { Draw(1, height: 2, $$ } }";
    let list = complete(source);
    let found = labels(&list);
    has_all(&found, &["width:", "fill:", "label:"]);
    has_none(&found, &["height:"]);
    assert_eq!(item(&list, "fill:").filter_text.as_deref(), Some("fill"));
    let construct = complete("class P { public P(int hp) { } } class C { void M() { new P($$ } }");
    assert!(labels(&construct).contains(&"hp:"));
    let static_call = complete(
        "static class K { public static void Go(int speed) { } } class C { void M() { K.Go($$ } }",
    );
    assert!(labels(&static_call).contains(&"speed:"));
}

// MARK: - object initializers

#[test]
fn an_initializer_offers_the_members_it_can_still_set() {
    let source = "class P { public int X; public int Y { get; set; } public int Z { get; } \
                  public readonly int R; public static int S; public void Go() { } \
                  public int I { get; init; } }\n\
                  class C { void M() { var p = new P { X = 1, $$ }; } }";
    let list = complete(source);
    let found = labels(&list);
    has_all(&found, &["Y", "I"]);
    has_none(&found, &["X", "Z", "R", "S", "Go", "if", "C", "new"]);

    let collection = complete(
        "using System.Collections.Generic;\nclass C { int local; void M() { var p = new List<int> { 1, $$ }; } }",
    );
    has_none(&labels(&collection), &["Count", "Add"]);
    assert!(labels(&collection).contains(&"local"));
}

// MARK: - import completion

#[test]
fn types_from_namespaces_not_imported_bring_their_using() {
    let others = [(
        "Tools.cs",
        "namespace Lib.Tools { public class Hammer { } public class Saw { } }",
    )];
    let (list, _) = complete_with(
        &others,
        "using System;\nusing Zed.Stuff;\n\nnamespace Zed.Stuff { class Q { } }\n\
         class C { void M() { Ham$$ } }",
    );
    let hammer = item(&list, "Hammer");
    assert!(hammer.rank > item(&list, "C").rank);
    assert!(hammer.detail.contains("Lib.Tools"), "{}", hammer.detail);
    assert_eq!(hammer.additional_edits.len(), 1);
    let edit = &hammer.additional_edits[0];
    assert_eq!(edit.text, "using Lib.Tools;\n");
    // Between `System` and `Zed.Stuff`.
    assert_eq!(edit.span.start(), "using System;\n".len() as u32);
    // Only names the word could start.
    has_none(&labels(&list), &["Saw"]);

    let (fresh, _) = complete_with(&others, "class C { void M() { Sa$$ } }");
    let saw = item(&fresh, "Saw");
    assert_eq!(saw.additional_edits[0].span.start(), 0);
    assert_eq!(saw.additional_edits[0].text, "using Lib.Tools;\n\n");

    // Already imported: offered plainly.
    let (imported, _) = complete_with(&others, "using Lib.Tools;\nclass C { void M() { Sa$$ } }");
    assert!(item(&imported, "Saw").additional_edits.is_empty());
}

#[test]
fn extension_methods_from_namespaces_not_imported_follow_a_dot() {
    let others = [(
        "Ext.cs",
        "namespace Lib.Text { public static class Words { public static int CountWords(this string s) => 0; \
         public static int Twice(this int i) => i * 2; } }",
    )];
    let (list, _) = complete_with(&others, "class C { void M(string s) { s.Cou$$ } }");
    let found = item(&list, "CountWords");
    assert_eq!(found.additional_edits[0].text, "using Lib.Text;\n\n");
    has_none(&labels(&list), &["Twice"]);
}

// MARK: - documentation comments

#[test]
fn documentation_offers_sections_and_undocumented_parameters() {
    let source = "class C {\n    /// <summary>Adds.</summary>\n    /// <param name=\"a\">A.</param>\n    /// <$$\n    \
                  int Add<T>(int a, int b) => a + b;\n}";
    let list = complete(source);
    let found = labels(&list);
    has_all(
        &found,
        &[
            "param name=\"b\"",
            "typeparam name=\"T\"",
            "returns",
            "remarks",
            "inheritdoc",
        ],
    );
    has_none(&found, &["summary", "param name=\"a\"", "value", "if", "C"]);
    let returns = item(&list, "returns");
    assert_eq!(returns.insert_text.as_deref(), Some("returns></returns>"));
    assert_eq!(returns.caret, Some("returns>".len() as u32));
}

#[test]
fn documentation_offers_inline_tags_inside_a_section_and_names_in_quotes() {
    let inside = complete("class C {\n    /// <summary>Uses <$$\n    void M(int a) { }\n}");
    has_all(
        &labels(&inside),
        &["c", "paramref name=\"a\"", "see", "para"],
    );
    has_none(&labels(&inside), &["summary", "returns"]);
    let names =
        complete("class C {\n    /// <param name=\"$$\n    void M(int count, int size) { }\n}");
    assert_eq!(labels(&names), vec!["count", "size"]);
}

// MARK: - directives

#[test]
fn directives_are_offered_after_a_hash() {
    let list = complete("class C {\n#$$\n}");
    has_all(
        &labels(&list),
        &["region", "endregion", "if", "pragma", "nullable"],
    );
    let pragma = complete("#pragma warning $$\nclass C { }");
    assert_eq!(labels(&pragma), vec!["disable", "restore"]);
    let condition = complete("#define FEATURE\n#if $$\nclass C { }\n#endif");
    has_all(&labels(&condition), &["DEBUG", "FEATURE", "TRACE"]);
    has_none(&labels(&condition), &["C", "class"]);
}

// MARK: - snippets

#[test]
fn snippets_go_where_what_they_write_can_go() {
    let statement = complete("class C { void M() {\n        $$\n    } }");
    let cw = statement
        .items
        .iter()
        .find(|item| item.label == "cw" && item.kind == CompletionKind::Snippet)
        .expect("cw");
    assert!(cw.is_snippet);
    assert_eq!(cw.insert_text.as_deref(), Some("Console.WriteLine();"));
    assert_eq!(cw.caret, Some("Console.WriteLine(".len() as u32));
    assert!(!labels(&statement).contains(&"prop"));

    let member = complete("class Player {\n    $$\n}");
    let ctor = member
        .items
        .iter()
        .find(|item| item.label == "ctor")
        .expect("ctor");
    assert_eq!(
        ctor.insert_text.as_deref(),
        Some("public Player()\n    {\n        \n    }")
    );
    has_all(&labels(&member), &["prop", "svm"]);
    assert!(!labels(&member).contains(&"cw"));
}

// MARK: - names

#[test]
fn a_new_name_is_suggested_from_its_type() {
    let others = [("Types.cs", "class StringBuilder { } class Item { }")];
    let (built, _) = complete_with(&others, "class C { void M() { StringBuilder $$ } }");
    assert!(built.suggestion_mode);
    assert_eq!(labels(&built), vec!["stringBuilder", "builder"]);

    let (number, _) = complete_with(&others, "class C { void M() { int $$ } }");
    assert!(labels(&number).contains(&"count"));
    assert!(number.suggestion_mode);

    let (list, _) = complete_with(
        &others,
        "using System.Collections.Generic;\nclass C { void M() { List<Item> $$ } }",
    );
    assert_eq!(list.items[0].label, "items");

    let (parameter, _) = complete_with(&others, "class C { void M(Item $$) { } }");
    assert_eq!(item(&parameter, "item").kind, CompletionKind::Parameter);

    let (property, _) = complete_with(&others, "class C { public Item $$ }");
    assert_eq!(property.items[0].label, "Item");

    // A value followed by a space is not a declaration.
    let (value, _) = complete_with(&others, "class C { void M(int x) { x $$ } }");
    assert!(!value.suggestion_mode);
    has_all(&keywords(&value), &["is", "as", "switch"]);
}

// MARK: - description

#[test]
fn a_description_is_the_documentation_of_the_item() {
    let text = "class C {\n    /// <summary>Heals the player.</summary>\n    void Heal() { }\n    \
                void M() { He }\n}";
    let semantic = compile(&[("Main.cs", text)], false).expect("compiled");
    let offset = (text.find("He }").expect("typed") + 2) as u32;
    let description = semantic
        .completion_description(Path::new("/p/Main.cs"), offset, None, "Heal")
        .expect("described");
    assert_eq!(description.summary, "Heals the player.");
    assert_eq!(description.signature, "void Heal()");
    let keyword = semantic
        .completion_description(Path::new("/p/Main.cs"), offset, None, "if")
        .expect("described");
    assert_eq!(keyword.signature, "if keyword");
}

#[test]
fn keywords_used_as_names_are_escaped() {
    let list = complete("class C { void M(int @class) { var x = $$ } }");
    let escaped = list
        .items
        .iter()
        .find(|item| item.label == "class" && item.kind == CompletionKind::Parameter)
        .expect("the parameter");
    assert_eq!(escaped.insert_text.as_deref(), Some("@class"));
}

#[test]
#[ignore = "a measurement"]
fn a_dot_stays_fast() {
    let mut source = String::new();
    for index in 0..400 {
        source.push_str(&format!(
            "namespace N{index} {{ public class T{index} {{ public int F{index}; public void M{index}() {{ }} }} \
             public static class E{index} {{ public static int X{index}(this string s) => 0; }} }}\n"
        ));
    }
    let main = "class C { void M(N1.T1 t, string s) { t.F; s.X } }";
    let semantic = compile(&[("Big.cs", &source), ("Main.cs", main)], false).expect("compiled");
    for (marker, into) in [("t.F", 3), ("s.X", 3)] {
        let offset = (main.find(marker).expect("marker") + into) as u32;
        // The first question builds the import index; the rest is what
        // typing costs.
        let _ = semantic.completions(Path::new("/p/Main.cs"), offset, None);
        let started = std::time::Instant::now();
        let list = semantic
            .completions(Path::new("/p/Main.cs"), offset, None)
            .expect("completed");
        println!(
            "{marker}: {} items in {:?}",
            list.items.len(),
            started.elapsed()
        );
    }
}

#[test]
fn a_case_label_cut_before_the_next_line_offers_the_enums_members() {
    // `case Kind.` typed above `Play(...)`: to the parser a pattern of type
    // `Kind.Play`, and the enum's members are what was meant.
    let list = complete(
        "enum Kind { DefaultState, Stop }\n\
         class C { void Play(int i) { } void M(Kind k) { switch (k) {\n\
         case Kind.$$\n\
             Play(1);\n\
             break; } } }",
    );
    has_all(&labels(&list), &["DefaultState", "Stop"]);
}
