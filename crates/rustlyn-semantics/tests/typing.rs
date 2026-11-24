//! Binding method bodies: the type of each expression, what each name refers
//! to, and what goes wrong.

use rustlyn_diagnostics::ErrorCode;
use rustlyn_semantics::{BoundSymbol, Compilation, SemanticModel};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, parse};
use rustlyn_text::SourceText;

fn compile(text: &str) -> Compilation {
    Compilation::create(vec![parse(SourceText::new("Program.cs", text))])
}

/// Compiles a method body and returns the compilation plus its model.
fn in_method(body: &str) -> Compilation {
    compile(&format!(
        "using System;\nusing System.Collections.Generic;\nclass C {{ void M() {{ {body} }} }}"
    ))
}

fn source_root(compilation: &Compilation) -> SyntaxNode {
    compilation.source_trees()[0].root()
}

/// The type of the last expression statement in a method body.
fn type_of_last_expression(body: &str) -> String {
    let compilation = in_method(body);
    let model = SemanticModel::new(&compilation, 1);
    let expression = source_root(&compilation)
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::ExpressionStatement)
        .last()
        .and_then(|statement: SyntaxNode| statement.children().next())
        .expect("an expression statement");
    model.type_of(&expression).display(compilation.symbols())
}

/// The declared type of the local called `name`.
fn type_of_local(body: &str, name: &str) -> String {
    let compilation = in_method(body);
    let model = SemanticModel::new(&compilation, 1);
    let root = source_root(&compilation);
    let declarator = root
        .descendants()
        .find(|node| {
            node.kind() == SyntaxKind::VariableDeclarator
                && node
                    .child_token_of_kind(SyntaxKind::IdentifierToken)
                    .is_some_and(|token| token.text() == name)
        })
        .unwrap_or_else(|| panic!("no local named {name}"));
    let body = model
        .bound_body_containing(&declarator)
        .expect("the method body");
    let span = declarator
        .child_token_of_kind(SyntaxKind::IdentifierToken)
        .expect("the name")
        .span();
    match body.reference_at(span) {
        Some(BoundSymbol::Local(id)) => {
            body.locals[id.0 as usize].ty.display(compilation.symbols())
        }
        _ => panic!("{name} is not a local"),
    }
}

/// The errors reported for a body. The snippets declare locals they never
/// read, which Roslyn warns about; the warnings are the business of
/// `tests/diagnostics.rs`.
fn codes(body: &str) -> Vec<ErrorCode> {
    let compilation = in_method(body);
    compilation
        .semantic_diagnostics()
        .iter()
        .filter(|entry| entry.diagnostic.is_error())
        .map(|entry| entry.diagnostic.code())
        .collect()
}

// -- expression types ------------------------------------------------------

#[test]
fn literals_have_the_types_the_lexer_gave_them() {
    assert_eq!(type_of_last_expression("1;"), "int");
    assert_eq!(type_of_last_expression("1L;"), "long");
    assert_eq!(type_of_last_expression("1u;"), "uint");
    assert_eq!(type_of_last_expression("1.5;"), "double");
    assert_eq!(type_of_last_expression("1.5f;"), "float");
    assert_eq!(type_of_last_expression("'c';"), "char");
    assert_eq!(type_of_last_expression("\"s\";"), "string");
    assert_eq!(type_of_last_expression("true;"), "bool");
}

#[test]
fn arithmetic_promotes_both_operands_to_the_wider_type() {
    assert_eq!(type_of_last_expression("1 + 2;"), "int");
    assert_eq!(type_of_last_expression("1 + 2L;"), "long");
    assert_eq!(type_of_last_expression("1 + 2.5;"), "double");
    assert_eq!(type_of_last_expression("1.5f + 2.5;"), "double");
    // Anything narrower than int is computed as int.
    assert_eq!(type_of_last_expression("(short)1 + (short)2;"), "int");
    assert_eq!(type_of_last_expression("'a' + 1;"), "int");
}

#[test]
fn plus_concatenates_when_either_side_is_a_string() {
    assert_eq!(type_of_last_expression("\"a\" + 1;"), "string");
    assert_eq!(type_of_last_expression("1 + \"a\";"), "string");
}

#[test]
fn comparisons_and_logic_produce_bool() {
    assert_eq!(type_of_last_expression("1 < 2;"), "bool");
    assert_eq!(type_of_last_expression("1 == 2;"), "bool");
    assert_eq!(type_of_last_expression("true && false;"), "bool");
    assert_eq!(type_of_last_expression("!true;"), "bool");
    assert_eq!(type_of_last_expression("1 is int;"), "bool");
}

#[test]
fn shifts_keep_the_type_of_their_left_operand() {
    assert_eq!(type_of_last_expression("1L << 2;"), "long");
    assert_eq!(type_of_last_expression("1 << 2L;"), "int");
}

#[test]
fn a_conditional_takes_the_type_both_branches_convert_to() {
    assert_eq!(type_of_last_expression("true ? 1 : 2;"), "int");
    assert_eq!(type_of_last_expression("true ? 1 : 2L;"), "long");
}

// -- locals ----------------------------------------------------------------

#[test]
fn var_takes_the_type_of_its_initializer() {
    assert_eq!(type_of_local("var x = 1;", "x"), "int");
    assert_eq!(type_of_local("var x = \"s\";", "x"), "string");
    assert_eq!(type_of_local("var x = new List<int>();", "x"), "List<int>");
    assert_eq!(type_of_local("var x = 1 + 2.0;", "x"), "double");
}

#[test]
fn a_declared_type_wins_over_the_initializer() {
    assert_eq!(type_of_local("long x = 1;", "x"), "long");
    assert_eq!(type_of_local("double x = 1;", "x"), "double");
}

#[test]
fn foreach_takes_the_element_type_of_the_collection() {
    assert_eq!(
        type_of_local(
            "var list = new List<string>(); foreach (var item in list) { }",
            "list"
        ),
        "List<string>"
    );
    let compilation = in_method(
        "int[] numbers = null; foreach (var n in numbers) { System.Console.WriteLine(n); }",
    );
    let model = SemanticModel::new(&compilation, 1);
    let name = source_root(&compilation)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IdentifierName && node.text() == "n")
        .expect("the loop variable in use");
    assert_eq!(model.type_of(&name).display(compilation.symbols()), "int");
}

#[test]
fn a_pattern_declares_a_variable_for_the_rest_of_the_statement() {
    let compilation =
        in_method("object o = null; if (o is string s) { System.Console.WriteLine(s.Length); }");
    let model = SemanticModel::new(&compilation, 1);
    let use_of_s = source_root(&compilation)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IdentifierName && node.text() == "s")
        .expect("the pattern variable in use");
    assert_eq!(
        model.type_of(&use_of_s).display(compilation.symbols()),
        "string"
    );
}

// -- members ---------------------------------------------------------------

#[test]
fn member_access_finds_the_members_type() {
    assert_eq!(type_of_last_expression("\"abc\".Length;"), "int");
    assert_eq!(type_of_last_expression("new List<int>().Count;"), "int");
    assert_eq!(type_of_last_expression("Math.PI;"), "double");
}

#[test]
fn a_generic_members_type_is_substituted_through_its_receiver() {
    // List<T>.this[int] is declared as returning T.
    assert_eq!(type_of_last_expression("new List<string>()[0];"), "string");
    assert_eq!(type_of_last_expression("new List<int>()[0];"), "int");
    assert_eq!(
        type_of_last_expression("new Dictionary<string, List<int>>()[\"k\"];"),
        "List<int>"
    );
}

#[test]
fn a_call_has_the_return_type_of_the_method_it_picked() {
    assert_eq!(type_of_last_expression("Math.Abs(1);"), "int");
    assert_eq!(type_of_last_expression("Math.Abs(1.5);"), "double");
    assert_eq!(type_of_last_expression("\"a\".Substring(1);"), "string");
    assert_eq!(type_of_last_expression("Console.ReadLine();"), "string");
}

#[test]
fn overload_resolution_prefers_an_exact_match() {
    let compilation = in_method("Math.Abs(1);");
    let model = SemanticModel::new(&compilation, 1);
    let call = source_root(&compilation)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IdentifierName && node.text() == "Abs")
        .expect("the method name");
    let Some(BoundSymbol::Declared(method)) = model.referenced_symbol(&call) else {
        panic!("the call should resolve to a method")
    };
    let symbols = compilation.symbols();
    let parameter = symbols.get(method).as_method().unwrap().parameters[0];
    assert_eq!(
        model.type_of_symbol(parameter).display(symbols),
        "int",
        "Abs(int) should win over Abs(double) for an int argument"
    );
}

#[test]
fn a_delegate_variable_can_be_called() {
    assert_eq!(
        type_of_last_expression("Func<int, string> f = null; f(1);"),
        "string"
    );
    assert_eq!(
        type_of_local("Func<int, string> f = null;", "f"),
        "Func<int, string>"
    );
}

#[test]
fn out_declarations_bring_a_variable_into_scope() {
    let compilation =
        in_method("if (int.TryParse(\"1\", out int value)) { Console.WriteLine(value); }");
    assert!(
        compilation.semantic_diagnostics().is_empty(),
        "{:?}",
        compilation
            .semantic_diagnostics()
            .iter()
            .map(|entry| compilation.render(entry))
            .collect::<Vec<_>>()
    );
    let model = SemanticModel::new(&compilation, 1);
    let use_of_value = source_root(&compilation)
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::IdentifierName && node.text() == "value")
        .last()
        .expect("the out variable in use");
    assert_eq!(
        model.type_of(&use_of_value).display(compilation.symbols()),
        "int"
    );
}

#[test]
fn lambda_parameters_are_in_scope_in_the_body() {
    let compilation = in_method("Func<int, int> square = x => x * x;");
    assert!(
        compilation.semantic_diagnostics().is_empty(),
        "{:?}",
        compilation
            .semantic_diagnostics()
            .iter()
            .map(|entry| compilation.render(entry))
            .collect::<Vec<_>>()
    );
}

// -- diagnostics -----------------------------------------------------------

#[test]
fn an_impossible_conversion_is_reported() {
    assert_eq!(
        codes("int x = \"text\";"),
        vec![ErrorCode::ErrNoImplicitConv]
    );
    assert_eq!(codes("string s = 1;"), vec![ErrorCode::ErrNoImplicitConv]);
    // Widening is fine in either order of declaration.
    assert!(codes("long x = 1;").is_empty());
    assert!(codes("double d = 1;").is_empty());
    assert!(codes("object o = \"s\";").is_empty());
    assert!(codes("object o = 1;").is_empty(), "boxing is implicit");
}

#[test]
fn a_condition_has_to_be_a_bool() {
    assert_eq!(codes("if (1) { }"), vec![ErrorCode::ErrNoImplicitConv]);
    assert!(codes("if (1 == 1) { }").is_empty());
}

#[test]
fn an_unknown_name_is_reported() {
    assert_eq!(codes("nonesuch = 1;"), vec![ErrorCode::ErrNameNotInContext]);
    assert_eq!(
        codes("var x = missing;"),
        vec![ErrorCode::ErrNameNotInContext]
    );
}

#[test]
fn an_unknown_member_is_reported() {
    assert_eq!(
        codes("\"a\".Nonesuch;"),
        vec![ErrorCode::ErrNoSuchMemberOrExtension]
    );
    assert_eq!(
        codes("\"a\".Nonesuch();"),
        vec![ErrorCode::ErrNoSuchMemberOrExtension]
    );
}

#[test]
fn a_call_with_the_wrong_number_of_arguments_is_reported() {
    assert_eq!(
        codes("Console.WriteLine(1, 2, 3);"),
        vec![ErrorCode::ErrBadArgCount]
    );
    assert!(codes("Console.WriteLine();").is_empty());
    assert!(codes("Console.WriteLine(1);").is_empty());
}

#[test]
fn a_redeclared_local_is_reported() {
    assert_eq!(
        codes("int a = 1; int a = 2;"),
        vec![ErrorCode::ErrLocalDuplicate]
    );
    // A new scope is a new name.
    assert!(codes("int a = 1; { } if (true) { int b = 2; }").is_empty());
    // A lambda or a local function hides what is around it rather than
    // clashing with it; a redeclaration inside one is still one.
    assert!(codes("int a = 1; Func<int, int> f = x => { int a = x; return a; };").is_empty());
    assert!(codes("int a = 1; int g(int x) { int a = x; return a; } g(a);").is_empty());
    assert_eq!(
        codes("int g(int x) { int a = x; int a = 2; return a; } g(1);"),
        vec![ErrorCode::ErrLocalDuplicate]
    );
}

#[test]
fn an_operator_that_does_not_apply_is_reported() {
    assert_eq!(
        codes("var x = \"a\" - \"b\";"),
        vec![ErrorCode::ErrBadBinaryOps]
    );
    assert!(codes("var x = \"a\" + \"b\";").is_empty());
}

#[test]
fn one_mistake_does_not_turn_into_several() {
    // Once `missing` is reported, everything downstream of it is an error type
    // that converts to anything, so nothing else is said about it.
    assert_eq!(
        codes("var x = missing; int y = x; string s = x;"),
        vec![ErrorCode::ErrNameNotInContext]
    );
}

#[test]
fn a_realistic_method_binds_without_complaint() {
    let compilation = compile(
        "using System;
         using System.Collections.Generic;

         class Basket
         {
             private readonly List<string> _items = new List<string>();

             public int Count => _items.Count;

             public void Add(string item)
             {
                 if (item == null) { throw new ArgumentException(\"item\"); }
                 _items.Add(item);
             }

             public string Describe()
             {
                 var total = 0;
                 foreach (var item in _items)
                 {
                     total = total + item.Length;
                 }
                 string label = total > 10 ? \"long\" : \"short\";
                 return label + \" (\" + Count + \")\";
             }
         }",
    );
    let rendered: Vec<_> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(rendered.is_empty(), "{rendered:?}");
}

// -- generic methods -------------------------------------------------------

/// The type of the last expression in a body, with helper methods in scope.
fn type_with_helpers(body: &str) -> String {
    let compilation = compile(&format!(
        "using System;\nusing System.Collections.Generic;\n\
         class C {{\n\
             static T Echo<T>(T value) {{ return value; }}\n\
             static T Pick<T>(T[] items) {{ return items[0]; }}\n\
             static T FromList<T>(List<T> items) {{ return items[0]; }}\n\
             static U Map<T, U>(T from, U to) {{ return to; }}\n\
             void M() {{ {body} }}\n\
         }}"
    ));
    let model = SemanticModel::new(&compilation, 1);
    let expression = source_root(&compilation)
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::ExpressionStatement)
        .last()
        .and_then(|statement: SyntaxNode| statement.children().next())
        .expect("an expression statement");
    model.type_of(&expression).display(compilation.symbols())
}

#[test]
fn a_generic_methods_type_arguments_are_inferred_from_its_arguments() {
    assert_eq!(type_with_helpers("Echo(1);"), "int");
    assert_eq!(type_with_helpers("Echo(\"s\");"), "string");
    // Written out, inference has nothing to do.
    assert_eq!(type_with_helpers("Echo<long>(1);"), "long");
    // Through the shape of the parameter, not just its identity.
    assert_eq!(type_with_helpers("Pick(new int[1]);"), "int");
    assert_eq!(type_with_helpers("FromList(new List<string>());"), "string");
    // Two parameters, inferred independently.
    assert_eq!(type_with_helpers("Map(1, \"s\");"), "string");
}

#[test]
fn a_type_argument_that_cannot_be_inferred_is_an_error() {
    // `null` says nothing about `T`, so there is no overload to pick.
    let compilation =
        compile("class C { static T Echo<T>(T value) { return value; } void M() { Echo(null); } }");
    assert_eq!(
        compilation
            .semantic_diagnostics()
            .iter()
            .map(|entry| entry.diagnostic.code())
            .collect::<Vec<_>>(),
        vec![ErrorCode::ErrCantInferMethTypeArgs]
    );
}

#[test]
fn a_pointer_walks_in_elements_and_reads_through_itself() {
    // Everything here binds and nothing here is emitted: the point is that
    // the types come out right, so a file full of unsafe code stops burying
    // the diagnostics that matter.
    let compilation = compile(
        r#"
        unsafe class Pointers
        {
            static T Load<T>(T* source) { return *source; }

            static void M(byte* buffer, ulong* accumulators, string text, byte[] bytes)
            {
                byte* end = buffer + 3;
                ulong* next = accumulators + 4;
                long distance = end - buffer;
                byte first = buffer[2];
                byte read = *buffer;
                byte** where = &buffer;
                ulong one = Load(accumulators);
                fixed (char* c = text) { char start = *c; }
                fixed (byte* b = bytes) { byte start = *b; }
            }
        }
        "#,
    );
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn a_static_local_function_declares_names_of_its_own() {
    // Roslyn leans on this: a `static` local function cannot reach the locals
    // around it, so the name it declares is its own whatever the method
    // holding it called something. A local function without the keyword
    // *does* reach them, and reads them.
    let reported = codes(
        r#"
        int total = 0;
        string path = "a";
        total = Count();
        path = Resolve();

        static string Resolve()
        {
            string path = "b";
            return path;
        }

        int Count()
        {
            return total + 1;
        }
        "#,
    );
    assert!(reported.is_empty(), "{reported:?}");
}

#[test]
fn a_tuple_is_a_value_with_a_type() {
    // `(a, b)` on the right of an `=` is not a deconstruction: it has a type,
    // which an overload and a lambda's return both have to see. The element
    // names are for the reader — the runtime never sees them — so two tuples
    // that name their elements differently are one type.
    assert_eq!(
        type_of_local("var pair = (1, \"two\");", "pair"),
        "(int, string)"
    );
    assert_eq!(
        type_of_local("var named = (count: 1, name: \"two\");", "named"),
        "(int count, string name)"
    );
    assert!(
        codes("(int count, string name) pair = (1, \"two\");").is_empty(),
        "names do not stand in the way of a conversion"
    );
}

#[test]
fn a_switch_block_is_one_declaration_space_with_sections_beside_it() {
    // A local declared in one section is in scope in the next — Roslyn's
    // command-line parser writes `string unquoted;` in one `case` and assigns
    // to it in another — while the variables a label declares belong to its
    // own section, so two sections may both write `case string s:`.
    let reported = codes(
        r#"
        object value = null;
        int kind = 1;
        switch (kind)
        {
            case 1:
                string held = "one";
                Console.WriteLine(held);
                break;
            case 2:
                held = "two";
                Console.WriteLine(held);
                break;
        }
        switch (value)
        {
            case string s:
                Console.WriteLine(s.Length);
                break;
            case int n:
                Console.WriteLine(n);
                break;
        }
        "#,
    );
    assert!(reported.is_empty(), "{reported:?}");
}

#[test]
fn nameof_in_a_pattern_is_a_constant() {
    // `nameof` is a contextual keyword, and an invocation of it is a constant
    // expression rather than a shape to match on a type of that name.
    let reported = codes(
        r#"
        string feature = "a";
        int found = feature switch
        {
            nameof(System.Object) => 1,
            _ => 0,
        };
        Console.WriteLine(found);
        "#,
    );
    assert!(reported.is_empty(), "{reported:?}");
}
