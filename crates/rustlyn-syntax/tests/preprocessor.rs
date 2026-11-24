//! Preprocessor directives, interpolated strings and raw strings — the three
//! places where the lexer has to be more than a scanner.

use rustlyn_diagnostics::ErrorCode;
use rustlyn_syntax::{ParseOptions, SyntaxKind, SyntaxTree, TokenValue, parse, parse_with};
use rustlyn_text::SourceText;

fn tree_of(text: &str) -> SyntaxTree {
    parse(SourceText::new("Test.cs", text))
}

fn tree_with(text: &str, symbols: &[&str]) -> SyntaxTree {
    parse_with(
        SourceText::new("Test.cs", text),
        &ParseOptions::with_symbols(symbols.iter().copied()),
    )
}

/// The trivia kinds in the file, in order.
fn trivia_kinds(tree: &SyntaxTree) -> Vec<SyntaxKind> {
    tree.root()
        .descendant_tokens()
        .flat_map(|token| {
            token
                .leading_trivia()
                .into_iter()
                .chain(token.trailing_trivia())
                .map(|trivia| trivia.kind())
                .collect::<Vec<_>>()
        })
        .collect()
}

/// The names of the types declared in the file.
fn type_names(tree: &SyntaxTree) -> Vec<String> {
    tree.root()
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::ClassDeclaration)
        .filter_map(|class| {
            class
                .child_token_of_kind(SyntaxKind::IdentifierToken)
                .map(|token| token.text().to_string())
        })
        .collect()
}

// -- directives ------------------------------------------------------------

#[test]
fn an_undefined_symbol_switches_the_branch_off() {
    let text = "#if DEBUG\nclass A {}\n#else\nclass B {}\n#endif\n";
    let tree = tree_of(text);
    assert_eq!(tree.text(), text);
    assert_eq!(type_names(&tree), vec!["B"]);
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
}

#[test]
fn a_defined_symbol_switches_it_on() {
    let text = "#if DEBUG\nclass A {}\n#else\nclass B {}\n#endif\n";
    let tree = tree_with(text, &["DEBUG"]);
    assert_eq!(tree.text(), text);
    assert_eq!(type_names(&tree), vec!["A"]);
}

#[test]
fn only_the_first_true_branch_is_taken() {
    let text = "\
#if A
class First {}
#elif B
class Second {}
#elif C
class Third {}
#else
class Fourth {}
#endif
";
    assert_eq!(type_names(&tree_with(text, &["B", "C"])), vec!["Second"]);
    assert_eq!(type_names(&tree_with(text, &["C"])), vec!["Third"]);
    assert_eq!(type_names(&tree_with(text, &[])), vec!["Fourth"]);
    assert_eq!(tree_with(text, &["A"]).text(), text);
}

#[test]
fn nested_conditionals_inside_a_dead_branch_are_skipped_whole() {
    let text = "\
#if OFF
#if ON
class Inner {}
#endif
class Outer {}
#endif
class Live {}
";
    let tree = tree_with(text, &["ON"]);
    assert_eq!(tree.text(), text);
    assert_eq!(type_names(&tree), vec!["Live"]);
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
}

#[test]
fn conditions_understand_the_operators() {
    let text = "#if A && !B\nclass Yes {}\n#endif\n";
    assert_eq!(type_names(&tree_with(text, &["A"])), vec!["Yes"]);
    assert!(type_names(&tree_with(text, &["A", "B"])).is_empty());

    let text = "#if (A || B) && C\nclass Yes {}\n#endif\n";
    assert_eq!(type_names(&tree_with(text, &["B", "C"])), vec!["Yes"]);
    assert!(type_names(&tree_with(text, &["B"])).is_empty());
}

#[test]
fn define_and_undef_take_effect_from_where_they_are() {
    let text = "\
#define FLAG
#if FLAG
class On {}
#endif
#undef FLAG
#if FLAG
class Off {}
#endif
";
    assert_eq!(type_names(&tree_of(text)), vec!["On"]);
}

#[test]
fn dead_code_becomes_one_piece_of_trivia() {
    let text = "#if OFF\nthis is not even C#\n#endif\nclass A {}\n";
    let tree = tree_of(text);
    assert_eq!(tree.text(), text);
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    let kinds = trivia_kinds(&tree);
    assert!(kinds.contains(&SyntaxKind::IfDirectiveTrivia));
    assert!(kinds.contains(&SyntaxKind::DisabledTextTrivia));
    assert!(kinds.contains(&SyntaxKind::EndIfDirectiveTrivia));
}

#[test]
fn regions_and_pragmas_are_recognised_and_ignored() {
    let text = "\
#region Helpers
#pragma warning disable CS0168
#nullable enable
class A {}
#pragma warning restore CS0168
#endregion
";
    let tree = tree_of(text);
    assert_eq!(tree.text(), text);
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    assert_eq!(type_names(&tree), vec!["A"]);
    let kinds = trivia_kinds(&tree);
    assert!(kinds.contains(&SyntaxKind::RegionDirectiveTrivia));
    assert!(kinds.contains(&SyntaxKind::PragmaWarningDirectiveTrivia));
    assert!(kinds.contains(&SyntaxKind::NullableDirectiveTrivia));
}

#[test]
fn error_and_warning_directives_report_only_when_reached() {
    let tree = tree_of("#error do not build this\n");
    assert_eq!(tree.diagnostics().len(), 1);
    assert_eq!(tree.diagnostics()[0].code(), ErrorCode::ErrErrorDirective);
    assert_eq!(
        tree.diagnostics()[0].message(),
        "#error: 'do not build this'"
    );

    // The same directive inside a dead branch says nothing.
    let tree = tree_of("#if OFF\n#error unreachable\n#endif\n");
    assert!(tree.diagnostics().is_empty());
}

#[test]
fn a_hash_that_is_not_at_the_start_of_a_line_is_not_a_directive() {
    let text = "class A { } #if X\n";
    let tree = tree_of(text);
    assert_eq!(tree.text(), text);
    assert!(
        !trivia_kinds(&tree).contains(&SyntaxKind::IfDirectiveTrivia),
        "a directive must own its line"
    );
}

#[test]
fn an_unclosed_conditional_is_reported() {
    let tree = tree_of("#if A\nclass A {}\n");
    assert!(
        tree.diagnostics()
            .iter()
            .any(|d| d.code() == ErrorCode::ErrEndifDirectiveExpected)
    );
}

// -- interpolated strings --------------------------------------------------

/// The shape of the first interpolated string in `text`.
fn interpolation_shape(text: &str) -> String {
    let source = format!("class C {{ void M() {{ var s = {text}; }} }}");
    let tree = tree_of(&source);
    assert!(!tree.has_errors(), "{text:?}: {:?}", tree.diagnostics());
    let string = tree
        .root()
        .descendants()
        .find(|node| node.kind() == SyntaxKind::InterpolatedStringExpression)
        .expect("an interpolated string");
    string
        .children_with_tokens()
        .map(|element| format!("{:?}", element.kind()))
        .collect::<Vec<_>>()
        .join(" ")
}

#[test]
fn an_interpolated_string_is_text_and_holes() {
    assert_eq!(
        interpolation_shape(r#"$"a{b}c""#),
        "InterpolatedStringStartToken InterpolatedStringText Interpolation \
         InterpolatedStringText InterpolatedStringEndToken"
    );
}

#[test]
fn a_hole_holds_a_real_expression() {
    let source = r#"class C { void M() { var s = $"{a + b * c}"; } }"#;
    let tree = tree_of(source);
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    assert!(
        tree.root()
            .descendants()
            .any(|node| node.kind() == SyntaxKind::MultiplyExpression),
        "the expression in the hole should be parsed like any other"
    );
}

#[test]
fn alignment_and_format_are_their_own_clauses() {
    let source = r#"class C { void M() { var s = $"{x,10:N2}"; } }"#;
    let tree = tree_of(source);
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    let kinds: Vec<_> = tree.root().descendants().map(|node| node.kind()).collect();
    assert!(kinds.contains(&SyntaxKind::InterpolationAlignmentClause));
    assert!(kinds.contains(&SyntaxKind::InterpolationFormatClause));
}

#[test]
fn a_colon_inside_parentheses_is_not_a_format_specifier() {
    // `$"{(a ? b : c)}"` — the colon belongs to the conditional.
    let source = r#"class C { void M() { var s = $"{(a ? b : c)}"; } }"#;
    let tree = tree_of(source);
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    assert!(
        tree.root()
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ConditionalExpression)
    );
    assert!(
        !tree
            .root()
            .descendants()
            .any(|node| node.kind() == SyntaxKind::InterpolationFormatClause)
    );
}

#[test]
fn doubled_braces_are_text() {
    assert_eq!(
        interpolation_shape(r#"$"{{literal}}""#),
        "InterpolatedStringStartToken InterpolatedStringText InterpolatedStringEndToken"
    );
}

#[test]
fn interpolated_strings_nest() {
    let source = r#"class C { void M() { var s = $"a{$"b{c}"}d"; } }"#;
    let tree = tree_of(source);
    assert_eq!(tree.text(), source);
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    assert_eq!(
        tree.root()
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::InterpolatedStringExpression)
            .count(),
        2
    );
}

#[test]
fn verbatim_interpolated_strings_may_span_lines() {
    for source in [
        "class C { void M() { var s = $@\"a\nb{c}\"; } }",
        "class C { void M() { var s = @$\"a\nb{c}\"; } }",
    ] {
        let tree = tree_of(source);
        assert_eq!(tree.text(), source);
        assert!(!tree.has_errors(), "{source:?}: {:?}", tree.diagnostics());
    }
}

#[test]
fn whitespace_inside_string_text_is_not_trivia() {
    let source = r#"class C { void M() { var s = $"  {x}  "; } }"#;
    let tree = tree_of(source);
    let texts: Vec<_> = tree
        .root()
        .descendant_tokens()
        .filter(|token| token.kind() == SyntaxKind::InterpolatedStringTextToken)
        .map(|token| token.text().to_string())
        .collect();
    assert_eq!(texts, vec!["  ", "  "]);
}

// -- raw strings -----------------------------------------------------------

#[test]
fn a_single_line_raw_string_needs_no_escapes() {
    let source = "class C { void M() { var s = \"\"\"he said \"hi\"\"\"\"; } }";
    let tree = tree_of(source);
    assert_eq!(tree.text(), source);
    let token = tree
        .root()
        .descendant_tokens()
        .find(|token| token.kind() == SyntaxKind::SingleLineRawStringLiteralToken)
        .expect("a raw string");
    assert_eq!(token.value(), &TokenValue::String("he said \"hi\"".into()));
}

#[test]
fn a_multi_line_raw_string_loses_the_indentation_of_its_fence() {
    let source = "\
class C
{
    void M()
    {
        var s = \"\"\"
            line one
              line two
            \"\"\";
    }
}
";
    let tree = tree_of(source);
    assert_eq!(tree.text(), source);
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    let token = tree
        .root()
        .descendant_tokens()
        .find(|token| token.kind() == SyntaxKind::MultiLineRawStringLiteralToken)
        .expect("a raw string");
    assert_eq!(
        token.value(),
        &TokenValue::String("line one\n  line two".into())
    );
}

// -- query expressions -----------------------------------------------------

#[test]
fn a_query_expression_is_parsed_clause_by_clause() {
    let source = "\
class C
{
    void M()
    {
        var q = from x in xs
                where x > 0
                let y = x * 2
                orderby y descending, x
                select new { x, y };
    }
}
";
    let tree = tree_of(source);
    assert_eq!(tree.text(), source);
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());

    let kinds: Vec<_> = tree.root().descendants().map(|node| node.kind()).collect();
    for wanted in [
        SyntaxKind::QueryExpression,
        SyntaxKind::FromClause,
        SyntaxKind::WhereClause,
        SyntaxKind::LetClause,
        SyntaxKind::OrderByClause,
        SyntaxKind::DescendingOrdering,
        SyntaxKind::SelectClause,
    ] {
        assert!(kinds.contains(&wanted), "missing {wanted:?}");
    }
}

#[test]
fn join_and_group_clauses() {
    let source = "\
class C
{
    void M()
    {
        var q = from a in xs
                join b in ys on a.Id equals b.Id into g
                group a by a.Key into k
                select k;
    }
}
";
    let tree = tree_of(source);
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    let kinds: Vec<_> = tree.root().descendants().map(|node| node.kind()).collect();
    assert!(kinds.contains(&SyntaxKind::JoinClause));
    assert!(kinds.contains(&SyntaxKind::JoinIntoClause));
    assert!(kinds.contains(&SyntaxKind::GroupClause));
    assert!(kinds.contains(&SyntaxKind::QueryContinuation));
}

#[test]
fn from_is_still_an_ordinary_name_elsewhere() {
    let source = "class C { void M() { var from = 1; from = from + 1; } }";
    let tree = tree_of(source);
    assert!(!tree.has_errors(), "{:?}", tree.diagnostics());
    assert!(
        !tree
            .root()
            .descendants()
            .any(|node| node.kind() == SyntaxKind::QueryExpression)
    );
}
