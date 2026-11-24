//! Lexer behaviour, checked against what `csc` does with the same input.

use rustlyn_diagnostics::ErrorCode;
use rustlyn_syntax::{LexResult, SyntaxKind, Token, TokenValue, tokenize};
use rustlyn_text::SourceText;

fn lex(text: &str) -> (SourceText, LexResult) {
    let source = SourceText::from_string(text);
    let result = tokenize(&source);
    (source, result)
}

/// The kinds of every token, end-of-file included.
fn kinds(text: &str) -> Vec<SyntaxKind> {
    lex(text).1.tokens.iter().map(|token| token.kind).collect()
}

/// The single token in `text`, which must lex to exactly one token.
fn single(text: &str) -> Token {
    let (_, result) = lex(text);
    assert_eq!(
        result.tokens.len(),
        2,
        "expected one token plus end-of-file in {text:?}, got {:?}",
        result.tokens.iter().map(|t| t.kind).collect::<Vec<_>>()
    );
    result.tokens.into_iter().next().unwrap()
}

fn codes(text: &str) -> Vec<ErrorCode> {
    lex(text)
        .1
        .diagnostics
        .as_slice()
        .iter()
        .map(|d| d.code())
        .collect()
}

const PROGRAM: &str = r#"// A greeting.
using System;

namespace Demo
{
    /// <summary>Says hello.</summary>
    public static class Program   // entry point
    {
        public static void Main(string[] args)
        {
            var name = args.Length > 0 ? args[0] : @"world";
            Console.WriteLine($"hello, {name}!");   /* trailing */
            int[] counts = { 1, 2_000, 0x1F, 0b1010 };
            double ratio = counts[0] / 3.5e-2;
            char tab = '\t';
            if (ratio >= 1.0 && name is not null) Console.WriteLine(ratio);
        }
    }
}
"#;

// -- full fidelity ---------------------------------------------------------

#[test]
fn tokens_reproduce_their_source() {
    for text in [
        "",
        " ",
        "\n",
        "class C {}",
        "int x = 1; // done\r\n",
        "/* unterminated",
        "@\"raw\r\nstring\"",
        "a\u{2028}b",
        PROGRAM,
    ] {
        let (source, result) = lex(text);
        let rebuilt: String = result
            .tokens
            .iter()
            .map(|token| token.full_text(&source))
            .collect();
        assert_eq!(rebuilt, text, "round trip failed for {text:?}");
    }
}

#[test]
fn full_spans_tile_the_file() {
    let (source, result) = lex(PROGRAM);
    let mut position = 0;
    for token in &result.tokens {
        assert_eq!(token.full_span.start(), position, "gap before {token:?}");
        assert!(token.full_span.contains_span(token.span));
        // Trivia sits inside the full span, on either side of the token.
        for trivia in &token.leading_trivia {
            assert!(token.full_span.contains_span(trivia.span));
            assert!(trivia.span.end() <= token.span.start());
        }
        for trivia in &token.trailing_trivia {
            assert!(token.full_span.contains_span(trivia.span));
            assert!(trivia.span.start() >= token.span.end());
        }
        position = token.full_span.end();
    }
    assert_eq!(position, source.len());
    assert!(result.tokens.last().unwrap().is_end_of_file());
}

#[test]
fn a_real_program_lexes_without_complaint() {
    let (_, result) = lex(PROGRAM);
    assert!(
        !result.diagnostics.has_errors(),
        "unexpected diagnostics: {:?}",
        result.diagnostics.as_slice()
    );
    assert!(!result.tokens.iter().any(|t| t.kind == SyntaxKind::BadToken));
}

// -- trivia ----------------------------------------------------------------

#[test]
fn trailing_trivia_stops_after_the_line_break() {
    let (source, result) = lex("int x; // note\nint y;");
    let semicolon = &result.tokens[2];
    assert_eq!(semicolon.kind, SyntaxKind::SemicolonToken);
    let trailing: Vec<_> = semicolon
        .trailing_trivia
        .iter()
        .map(|t| (t.kind, t.text(&source)))
        .collect();
    assert_eq!(
        trailing,
        vec![
            (SyntaxKind::WhitespaceTrivia, " "),
            (SyntaxKind::SingleLineCommentTrivia, "// note"),
            (SyntaxKind::EndOfLineTrivia, "\n"),
        ]
    );
    // The line break went to the semicolon, so the next token starts clean.
    assert!(result.tokens[3].leading_trivia.is_empty());
}

#[test]
fn documentation_comments_lead_the_next_token() {
    // Roslyn never puts a documentation comment in trailing trivia: it belongs
    // to whatever it documents.
    let (source, result) = lex("int x; /// <summary/>\nint y;");
    let semicolon = &result.tokens[2];
    assert_eq!(
        semicolon
            .trailing_trivia
            .iter()
            .map(|t| t.kind)
            .collect::<Vec<_>>(),
        vec![SyntaxKind::WhitespaceTrivia]
    );
    let next = &result.tokens[3];
    assert_eq!(next.kind, SyntaxKind::IntKeyword);
    assert_eq!(
        next.leading_trivia
            .iter()
            .map(|t| (t.kind, t.text(&source)))
            .collect::<Vec<_>>(),
        vec![
            (
                SyntaxKind::SingleLineDocumentationCommentTrivia,
                "/// <summary/>"
            ),
            (SyntaxKind::EndOfLineTrivia, "\n"),
        ]
    );
}

#[test]
fn comment_flavours() {
    let leading = |text: &str| lex(text).1.tokens[0].leading_trivia[0].kind;
    assert_eq!(leading("// plain\nx"), SyntaxKind::SingleLineCommentTrivia);
    assert_eq!(
        leading("/// doc\nx"),
        SyntaxKind::SingleLineDocumentationCommentTrivia
    );
    // Four slashes is a plain comment again, matching Roslyn.
    assert_eq!(
        leading("//// plain\nx"),
        SyntaxKind::SingleLineCommentTrivia
    );
    assert_eq!(leading("/* plain */ x"), SyntaxKind::MultiLineCommentTrivia);
    assert_eq!(
        leading("/** doc */ x"),
        SyntaxKind::MultiLineDocumentationCommentTrivia
    );
    assert_eq!(leading("/**/ x"), SyntaxKind::MultiLineCommentTrivia);
    assert_eq!(
        leading("/*** plain */ x"),
        SyntaxKind::MultiLineCommentTrivia
    );
}

#[test]
fn unterminated_block_comment_is_reported_once() {
    assert_eq!(codes("/* nope"), vec![ErrorCode::ErrOpenEndedComment]);
    assert_eq!(kinds("/* nope"), vec![SyntaxKind::EndOfFileToken]);
}

#[test]
fn crlf_is_a_single_end_of_line() {
    let (source, result) = lex("x\r\ny");
    let trivia = &result.tokens[0].trailing_trivia;
    assert_eq!(trivia.len(), 1);
    assert_eq!(trivia[0].kind, SyntaxKind::EndOfLineTrivia);
    assert_eq!(trivia[0].text(&source), "\r\n");
}

// -- identifiers and keywords ---------------------------------------------

#[test]
fn reserved_keywords_get_their_own_kind() {
    assert_eq!(single("class").kind, SyntaxKind::ClassKeyword);
    assert_eq!(single("__arglist").kind, SyntaxKind::ArgListKeyword);
}

#[test]
fn contextual_keywords_stay_identifiers() {
    let token = single("var");
    assert_eq!(token.kind, SyntaxKind::IdentifierToken);
    assert_eq!(token.contextual_kind, SyntaxKind::VarKeyword);
    assert!(token.is_keyword());

    let underscore = single("_");
    assert_eq!(underscore.kind, SyntaxKind::IdentifierToken);
    assert_eq!(underscore.contextual_kind, SyntaxKind::UnderscoreToken);

    // `dynamic` is an ordinary identifier as far as the lexer is concerned.
    let dynamic = single("dynamic");
    assert_eq!(dynamic.kind, SyntaxKind::IdentifierToken);
    assert_eq!(dynamic.contextual_kind, SyntaxKind::IdentifierToken);
}

#[test]
fn verbatim_identifiers_drop_the_at_sign() {
    let (source, result) = lex("@class");
    let token = &result.tokens[0];
    assert_eq!(token.kind, SyntaxKind::IdentifierToken);
    assert_eq!(token.text(&source), "@class");
    assert_eq!(token.value_text(&source), "class");
}

#[test]
fn unicode_escapes_spell_identifiers() {
    let (source, result) = lex("\\u0063lass");
    let token = &result.tokens[0];
    // An escaped keyword is an identifier, never the keyword itself.
    assert_eq!(token.kind, SyntaxKind::IdentifierToken);
    assert_eq!(token.value_text(&source), "class");
    assert!(!result.diagnostics.has_errors());
}

#[test]
fn identifiers_may_be_non_ascii() {
    let (source, result) = lex("int имя = 1;");
    let token = &result.tokens[1];
    assert_eq!(token.kind, SyntaxKind::IdentifierToken);
    assert_eq!(token.text(&source), "имя");
}

#[test]
fn a_bare_at_sign_is_reported() {
    assert_eq!(codes("@ x"), vec![ErrorCode::ErrExpectedVerbatimLiteral]);
    assert_eq!(
        kinds("@ x"),
        vec![
            SyntaxKind::BadToken,
            SyntaxKind::IdentifierToken,
            SyntaxKind::EndOfFileToken
        ]
    );
}

// -- punctuation -----------------------------------------------------------

#[test]
fn operators_take_the_longest_match() {
    assert_eq!(
        single(">>=").kind,
        SyntaxKind::GreaterThanGreaterThanEqualsToken
    );
    assert_eq!(
        single(">>>=").kind,
        SyntaxKind::GreaterThanGreaterThanGreaterThanEqualsToken
    );
    assert_eq!(
        single(">>>").kind,
        SyntaxKind::GreaterThanGreaterThanGreaterThanToken
    );
    assert_eq!(single("<<=").kind, SyntaxKind::LessThanLessThanEqualsToken);
    assert_eq!(single("??=").kind, SyntaxKind::QuestionQuestionEqualsToken);
    assert_eq!(single("=>").kind, SyntaxKind::EqualsGreaterThanToken);
    assert_eq!(single("->").kind, SyntaxKind::MinusGreaterThanToken);
    assert_eq!(single("::").kind, SyntaxKind::ColonColonToken);
    assert_eq!(single("..").kind, SyntaxKind::DotDotToken);
}

#[test]
fn nested_generics_lex_as_a_shift_for_the_parser_to_split() {
    // `List<List<int>>` ends in one token here; splitting it belongs to the
    // parser, which is the only place that knows a generic is being closed.
    assert_eq!(
        kinds("List<List<int>>"),
        vec![
            SyntaxKind::IdentifierToken,
            SyntaxKind::LessThanToken,
            SyntaxKind::IdentifierToken,
            SyntaxKind::LessThanToken,
            SyntaxKind::IntKeyword,
            SyntaxKind::GreaterThanGreaterThanToken,
            SyntaxKind::EndOfFileToken,
        ]
    );
}

#[test]
fn unknown_characters_become_bad_tokens() {
    assert_eq!(
        kinds("`"),
        vec![SyntaxKind::BadToken, SyntaxKind::EndOfFileToken]
    );
    let (_, result) = lex("`");
    assert_eq!(
        result.diagnostics.as_slice()[0].code(),
        ErrorCode::ErrUnexpectedCharacter
    );
    assert_eq!(
        result.diagnostics.as_slice()[0].message(),
        "Unexpected character '`'"
    );
}

// -- numeric literals ------------------------------------------------------

#[test]
fn integer_literals_pick_the_first_type_that_fits() {
    assert_eq!(single("0").value, TokenValue::Int32(0));
    assert_eq!(single("2147483647").value, TokenValue::Int32(i32::MAX));
    assert_eq!(
        single("2147483648").value,
        TokenValue::UInt32(2_147_483_648)
    );
    assert_eq!(single("4294967296").value, TokenValue::Int64(4_294_967_296));
    assert_eq!(
        single("9223372036854775808").value,
        TokenValue::UInt64(9_223_372_036_854_775_808)
    );
}

#[test]
fn integer_suffixes() {
    assert_eq!(single("1u").value, TokenValue::UInt32(1));
    assert_eq!(single("1U").value, TokenValue::UInt32(1));
    assert_eq!(single("1L").value, TokenValue::Int64(1));
    assert_eq!(single("1ul").value, TokenValue::UInt64(1));
    assert_eq!(single("1LU").value, TokenValue::UInt64(1));
}

#[test]
fn radix_prefixes_and_separators() {
    assert_eq!(single("0x1F").value, TokenValue::Int32(31));
    assert_eq!(single("0XffL").value, TokenValue::Int64(255));
    assert_eq!(single("0b1010").value, TokenValue::Int32(10));
    assert_eq!(single("1_000_000").value, TokenValue::Int32(1_000_000));
    assert_eq!(single("0x_FF").value, TokenValue::Int32(255));
}

#[test]
fn real_literals() {
    assert_eq!(single("1.5").value, TokenValue::Double(1.5));
    assert_eq!(single(".5").value, TokenValue::Double(0.5));
    assert_eq!(single("1e3").value, TokenValue::Double(1000.0));
    assert_eq!(single("3.5e-2").value, TokenValue::Double(0.035));
    assert_eq!(single("1.5f").value, TokenValue::Single(1.5));
    assert_eq!(single("1d").value, TokenValue::Double(1.0));
    assert_eq!(single("1.5m").value, TokenValue::Decimal("1.5".into()));
}

#[test]
fn a_dot_after_a_number_is_only_a_decimal_point_before_a_digit() {
    assert_eq!(
        kinds("1.ToString()"),
        vec![
            SyntaxKind::NumericLiteralToken,
            SyntaxKind::DotToken,
            SyntaxKind::IdentifierToken,
            SyntaxKind::OpenParenToken,
            SyntaxKind::CloseParenToken,
            SyntaxKind::EndOfFileToken,
        ]
    );
    assert_eq!(
        kinds("1..2"),
        vec![
            SyntaxKind::NumericLiteralToken,
            SyntaxKind::DotDotToken,
            SyntaxKind::NumericLiteralToken,
            SyntaxKind::EndOfFileToken,
        ]
    );
}

#[test]
fn an_e_that_starts_no_exponent_is_an_identifier() {
    assert_eq!(
        kinds("1em"),
        vec![
            SyntaxKind::NumericLiteralToken,
            SyntaxKind::IdentifierToken,
            SyntaxKind::EndOfFileToken,
        ]
    );
}

#[test]
fn malformed_numbers_are_reported() {
    assert_eq!(codes("0x"), vec![ErrorCode::ErrInvalidNumber]);
    assert_eq!(codes("1_"), vec![ErrorCode::ErrInvalidNumber]);
    assert_eq!(
        codes("18446744073709551616"),
        vec![ErrorCode::ErrIntOverflow]
    );
    assert_eq!(codes("1e400"), vec![ErrorCode::ErrFloatOverflow]);
    let (_, result) = lex("1e400");
    assert_eq!(
        result.diagnostics.as_slice()[0].message(),
        "Floating-point constant is outside the range of type 'double'"
    );
}

// -- string and character literals ----------------------------------------

#[test]
fn string_values_are_decoded() {
    assert_eq!(single(r#""abc""#).value, TokenValue::String("abc".into()));
    assert_eq!(
        single(r#""a\tbA\x41""#).value,
        TokenValue::String("a\tbAA".into())
    );
    assert_eq!(single(r#""""#).value, TokenValue::String("".into()));
}

#[test]
fn verbatim_strings_keep_line_breaks_and_double_quotes() {
    let token = single("@\"a\"\"b\nc\"");
    assert_eq!(token.kind, SyntaxKind::StringLiteralToken);
    assert_eq!(token.value, TokenValue::String("a\"b\nc".into()));
}

#[test]
fn utf8_suffix_changes_the_kind() {
    assert_eq!(
        single(r#""abc"u8"#).kind,
        SyntaxKind::Utf8StringLiteralToken
    );
    assert_eq!(single(r#""abc""#).kind, SyntaxKind::StringLiteralToken);
}

#[test]
fn surrogate_pairs_combine() {
    assert_eq!(
        single(r#""😀""#).value,
        TokenValue::String("\u{1F600}".into())
    );
}

#[test]
fn character_literals() {
    assert_eq!(single("'a'").value, TokenValue::Char('a'));
    assert_eq!(single(r"'\n'").value, TokenValue::Char('\n'));
    assert_eq!(single(r"'\''").value, TokenValue::Char('\''));
    assert_eq!(codes("''"), vec![ErrorCode::ErrEmptyCharConst]);
    assert_eq!(codes("'ab'"), vec![ErrorCode::ErrTooManyCharsInConst]);
    // A C# char holds one UTF-16 unit, so an astral character does not fit.
    assert_eq!(
        codes("'\u{1F600}'"),
        vec![ErrorCode::ErrTooManyCharsInConst]
    );
}

#[test]
fn unterminated_literals_are_reported() {
    assert_eq!(codes("\"abc"), vec![ErrorCode::ErrNewlineInConst]);
    // The literal ends at the line break, so the closing quote on the next
    // line opens a second, equally unterminated one.
    assert_eq!(
        codes("\"abc\ndef\""),
        vec![ErrorCode::ErrNewlineInConst, ErrorCode::ErrNewlineInConst]
    );
    assert_eq!(codes("'a"), vec![ErrorCode::ErrNewlineInConst]);
    assert_eq!(codes("@\"abc"), vec![ErrorCode::ErrUnterminatedStringLit]);
}

#[test]
fn unknown_escapes_are_reported_but_lexing_continues() {
    let (_, result) = lex(r#""a\qb""#);
    assert_eq!(
        result
            .diagnostics
            .as_slice()
            .iter()
            .map(|d| d.code())
            .collect::<Vec<_>>(),
        vec![ErrorCode::ErrIllegalEscape]
    );
    assert_eq!(result.tokens[0].kind, SyntaxKind::StringLiteralToken);
    assert_eq!(result.tokens[0].value, TokenValue::String("ab".into()));
}

// -- diagnostics -----------------------------------------------------------

#[test]
fn diagnostics_point_at_the_offending_text() {
    let source = SourceText::new("Program.cs", "class C\n{\n    int x = 1e400;\n}\n");
    let result = tokenize(&source);
    let diagnostic = &result.diagnostics.as_slice()[0];
    assert_eq!(source.slice(diagnostic.span()), "1e400");
    assert_eq!(
        diagnostic.display_with(&source).to_string(),
        "Program.cs(3,13): error CS0594: Floating-point constant is outside the range of type 'double'"
    );
}

// -- raw strings -----------------------------------------------------------

#[test]
fn a_multi_line_raw_string_closes_only_at_the_start_of_a_line() {
    let token = single("\"\"\"\n    a \"\"\" b\n    \"\"\"");
    assert_eq!(token.kind, SyntaxKind::MultiLineRawStringLiteralToken);
    assert_eq!(token.value, TokenValue::String("a \"\"\" b".into()));
}

#[test]
fn a_single_line_raw_string_closes_at_the_first_long_enough_run() {
    let token = single("\"\"\"he said \"hi\"\"\"\"");
    assert_eq!(token.kind, SyntaxKind::SingleLineRawStringLiteralToken);
    assert_eq!(token.value, TokenValue::String("he said \"hi\"".into()));
}

#[test]
fn a_raw_string_may_carry_the_utf8_suffix() {
    assert_eq!(
        single("\"\"\"a\"\"\"u8").kind,
        SyntaxKind::Utf8SingleLineRawStringLiteralToken
    );
}

#[test]
fn a_raw_interpolated_string_is_lexed_as_a_stream() {
    assert_eq!(
        kinds("$$\"\"\"a{{b}}c\"\"\""),
        vec![
            SyntaxKind::InterpolatedSingleLineRawStringStartToken,
            SyntaxKind::InterpolatedStringTextToken,
            SyntaxKind::OpenBraceToken,
            SyntaxKind::IdentifierToken,
            SyntaxKind::CloseBraceToken,
            SyntaxKind::InterpolatedStringTextToken,
            SyntaxKind::InterpolatedRawStringEndToken,
            SyntaxKind::EndOfFileToken,
        ]
    );
}

/// Files that end, or run into a brace, inside the format specifier of a
/// hole. Each once lexed forever: a token that took nothing, asked for again
/// at the same place (found by fuzzing, `examples/fuzz.rs` in rustlyn-ide).
#[test]
fn a_format_specifier_cut_short_still_ends_the_file() {
    for text in [
        "$\"{:",
        "$\"{x:N2",
        "$@\"{x:\nN2\n",
        "class C { string s = $@\"{a\n}\n{b: c",
        "$$\"\"\"{{x:}",
        "$$\"\"\"{{x:}\"\"\"",
        "$$\"\"\"{{x:} }}\"\"\"",
    ] {
        let (source, result) = lex(text);
        assert!(
            result.tokens.last().is_some_and(Token::is_end_of_file),
            "{text:?}"
        );
        let mut position = 0;
        for token in &result.tokens {
            assert_eq!(
                token.full_span.start(),
                position,
                "gap before {token:?} in {text:?}"
            );
            assert!(
                token.full_span.end() > position || token.is_end_of_file(),
                "a token that took nothing in {text:?}: {token:?}"
            );
            position = token.full_span.end();
        }
        assert_eq!(position, source.len(), "{text:?}");
    }
}

// -- directives ------------------------------------------------------------

#[test]
fn file_based_program_directives() {
    let (_, result) = lex("#!/usr/bin/env dotnet\n#:package A@1.0.0\nM();\n");
    assert!(result.diagnostics.as_slice().is_empty());
    let trivia: Vec<SyntaxKind> = result.tokens[0]
        .leading_trivia
        .iter()
        .map(|item| item.kind)
        .filter(|kind| *kind != SyntaxKind::EndOfLineTrivia)
        .collect();
    assert_eq!(
        trivia,
        vec![
            SyntaxKind::ShebangDirectiveTrivia,
            SyntaxKind::IgnoredDirectiveTrivia
        ]
    );
}
