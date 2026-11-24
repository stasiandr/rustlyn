//! Brace matching: the other half of the brace at the caret, for the editor
//! to highlight both. Roslyn's `BraceMatchingService`, from the parse alone.
//!
//! The pairs are the ones Roslyn knows: `{}`, `()` and `[]` wherever the
//! grammar puts them, `<>` of a type argument or type parameter list (never a
//! less-than), the quotes of a string or character literal and of an
//! interpolated string, the braces of an interpolation, and the directives
//! `#if`, `#elif`, `#else`, `#endif` and `#region`, `#endregion`.
//!
//! As in Roslyn, the caret may sit just before an opening brace or just
//! after a closing one — or, for that matter, just after an opening brace or
//! just before a closing one: the token on the right of the caret is tried
//! first, then the one on its left. A conditional directive matches the next
//! directive of its chain, and `#endif` the `#if` that began it, so that
//! asking again walks the chain round.

use rustlyn_syntax::{SyntaxKind as K, SyntaxNode, SyntaxToken, SyntaxTrivia};
use rustlyn_text::TextSpan;

/// Two delimiters that belong together, the earlier first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BracePair {
    pub open: TextSpan,
    pub close: TextSpan,
}

impl BracePair {
    fn ordered(one: TextSpan, other: TextSpan) -> Self {
        if one.start() <= other.start() {
            Self {
                open: one,
                close: other,
            }
        } else {
            Self {
                open: other,
                close: one,
            }
        }
    }
}

/// The pair the delimiter beside `position` belongs to.
#[must_use]
pub fn matching_braces(root: &SyntaxNode, position: u32) -> Option<BracePair> {
    let tokens: Vec<SyntaxToken> = root
        .descendant_tokens()
        .filter(|token| !token.span().is_empty())
        .collect();
    let right = tokens
        .iter()
        .find(|token| token.span().start() == position)
        .and_then(match_token);
    if right.is_some() {
        return right;
    }
    if let Some(found) = match_directive(root, position, true) {
        return Some(found);
    }
    let left = tokens
        .iter()
        .find(|token| token.span().end() == position)
        .and_then(match_token);
    if left.is_some() {
        return left;
    }
    match_directive(root, position, false)
}

fn match_token(token: &SyntaxToken) -> Option<BracePair> {
    let kind = token.kind();
    match kind {
        K::OpenBraceToken
        | K::CloseBraceToken
        | K::OpenParenToken
        | K::CloseParenToken
        | K::OpenBracketToken
        | K::CloseBracketToken => match_within_parent(token),
        K::LessThanToken | K::GreaterThanToken
            if matches!(
                token.parent().kind(),
                K::TypeArgumentList | K::TypeParameterList | K::FunctionPointerParameterList
            ) =>
        {
            match_within_parent(token)
        }
        K::StringLiteralToken
        | K::Utf8StringLiteralToken
        | K::SingleLineRawStringLiteralToken
        | K::MultiLineRawStringLiteralToken
        | K::Utf8SingleLineRawStringLiteralToken
        | K::Utf8MultiLineRawStringLiteralToken
        | K::CharacterLiteralToken => literal_quotes(token),
        K::InterpolatedStringStartToken
        | K::InterpolatedVerbatimStringStartToken
        | K::InterpolatedSingleLineRawStringStartToken
        | K::InterpolatedMultiLineRawStringStartToken
        | K::InterpolatedStringEndToken
        | K::InterpolatedRawStringEndToken => {
            let parent = token.parent();
            let start = parent.first_token()?;
            let end = parent.last_token().filter(|end| !end.is_missing())?;
            (start.span() != end.span()).then(|| BracePair::ordered(start.span(), end.span()))
        }
        _ => None,
    }
}

/// The counterpart of a bracket among its parent's own tokens, counting
/// nesting of the same kind.
fn match_within_parent(token: &SyntaxToken) -> Option<BracePair> {
    let (open, close) = match token.kind() {
        K::OpenBraceToken | K::CloseBraceToken => (K::OpenBraceToken, K::CloseBraceToken),
        K::OpenParenToken | K::CloseParenToken => (K::OpenParenToken, K::CloseParenToken),
        K::OpenBracketToken | K::CloseBracketToken => (K::OpenBracketToken, K::CloseBracketToken),
        K::LessThanToken | K::GreaterThanToken => (K::LessThanToken, K::GreaterThanToken),
        _ => return None,
    };
    let siblings: Vec<SyntaxToken> = token
        .parent()
        .child_tokens()
        .filter(|sibling| matches!(sibling.kind(), kind if kind == open || kind == close))
        .collect();
    let at = siblings.iter().position(|sibling| sibling == token)?;
    let mut depth = 0i32;
    if token.kind() == open {
        for sibling in &siblings[at..] {
            depth += if sibling.kind() == open { 1 } else { -1 };
            if depth == 0 {
                return (!sibling.is_missing())
                    .then(|| BracePair::ordered(token.span(), sibling.span()));
            }
        }
    } else {
        for sibling in siblings[..=at].iter().rev() {
            depth += if sibling.kind() == close { 1 } else { -1 };
            if depth == 0 {
                return (!sibling.is_missing())
                    .then(|| BracePair::ordered(sibling.span(), token.span()));
            }
        }
    }
    None
}

/// The opening and closing quotes of a literal: `"`, `@"`, `"""`, `'`, and
/// the `u8` that follows a UTF-8 string's closing quote.
fn literal_quotes(token: &SyntaxToken) -> Option<BracePair> {
    let text = token.text();
    let span = token.span();
    let quote = if token.kind() == K::CharacterLiteralToken {
        '\''
    } else {
        '"'
    };
    let prefix = text.find(quote)?;
    let opening = text[prefix..].chars().take_while(|&ch| ch == quote).count();
    let body = text.trim_end_matches("u8").trim_end_matches("U8");
    let closing = body.chars().rev().take_while(|&ch| ch == quote).count();
    // `""` is one quote each way; a raw string's run counts on both sides.
    let (opening, closing) = if opening == 2 && text.len() == prefix + 2 {
        (1, 1)
    } else {
        (opening.min(closing), opening.min(closing))
    };
    if opening == 0 || body.len() < prefix + opening + closing {
        return None;
    }
    let open = TextSpan::new(span.start(), (prefix + opening) as u32);
    let close = TextSpan::from_bounds(span.start() + (body.len() - closing) as u32, span.end());
    Some(BracePair::ordered(open, close))
}

// MARK: - directives

/// The `#` and the keyword of a directive: what gets highlighted.
fn directive_keyword(trivia: &SyntaxTrivia) -> TextSpan {
    let text = trivia.text();
    let after_hash = text.find('#').map_or(0, |at| at + 1);
    let rest = &text[after_hash..];
    let space = rest.len() - rest.trim_start().len();
    let word = rest
        .trim_start()
        .chars()
        .take_while(char::is_ascii_alphabetic)
        .count();
    TextSpan::new(trivia.span().start(), (after_hash + space + word) as u32)
}

fn match_directive(root: &SyntaxNode, position: u32, right: bool) -> Option<BracePair> {
    let mut directives: Vec<SyntaxTrivia> = Vec::new();
    for token in root.descendant_tokens() {
        for trivia in token
            .leading_trivia()
            .into_iter()
            .chain(token.trailing_trivia())
        {
            if matches!(
                trivia.kind(),
                K::IfDirectiveTrivia
                    | K::ElifDirectiveTrivia
                    | K::ElseDirectiveTrivia
                    | K::EndIfDirectiveTrivia
                    | K::RegionDirectiveTrivia
                    | K::EndRegionDirectiveTrivia
            ) {
                directives.push(trivia);
            }
        }
    }
    let at = directives.iter().position(|trivia| {
        let keyword = directive_keyword(trivia);
        if right {
            keyword.start() == position
        } else {
            keyword.end() == position
        }
    })?;

    // Chains of conditional directives, and pairs of regions, each found by
    // a stack.
    let mut chains: Vec<Vec<usize>> = Vec::new();
    let mut open_chains: Vec<usize> = Vec::new();
    let mut regions: Vec<usize> = Vec::new();
    let mut region_pairs: Vec<(usize, usize)> = Vec::new();
    for (index, trivia) in directives.iter().enumerate() {
        match trivia.kind() {
            K::IfDirectiveTrivia => {
                open_chains.push(chains.len());
                chains.push(vec![index]);
            }
            K::ElifDirectiveTrivia | K::ElseDirectiveTrivia => {
                if let Some(&chain) = open_chains.last() {
                    chains[chain].push(index);
                }
            }
            K::EndIfDirectiveTrivia => {
                if let Some(chain) = open_chains.pop() {
                    chains[chain].push(index);
                }
            }
            K::RegionDirectiveTrivia => regions.push(index),
            K::EndRegionDirectiveTrivia => {
                if let Some(start) = regions.pop() {
                    region_pairs.push((start, index));
                }
            }
            _ => {}
        }
    }
    let keyword = |index: usize| directive_keyword(&directives[index]);
    if let Some(&(start, end)) = region_pairs
        .iter()
        .find(|(start, end)| *start == at || *end == at)
    {
        return Some(BracePair::ordered(keyword(start), keyword(end)));
    }
    let chain = chains.iter().find(|chain| chain.contains(&at))?;
    if chain.len() < 2 {
        return None;
    }
    let place = chain.iter().position(|&index| index == at)?;
    let next = chain[(place + 1) % chain.len()];
    Some(BracePair::ordered(keyword(at), keyword(next)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustlyn_text::SourceText;

    /// The pair found with the caret at `|`, as the text of each half.
    fn pair(marked: &str) -> Option<(String, String)> {
        let position = marked.find('|').expect("a caret") as u32;
        let text = marked.replacen('|', "", 1);
        let root = rustlyn_syntax::parse(SourceText::new("A.cs", text.as_str())).root();
        let found = matching_braces(&root, position)?;
        let slice = |span: TextSpan| text[span.start() as usize..span.end() as usize].to_owned();
        Some((slice(found.open), slice(found.close)))
    }

    /// The pair found with the caret at `|`, as offsets of each half.
    fn offsets(marked: &str) -> Option<(u32, u32)> {
        let position = marked.find('|').expect("a caret") as u32;
        let text = marked.replacen('|', "", 1);
        let root = rustlyn_syntax::parse(SourceText::new("A.cs", text.as_str())).root();
        matching_braces(&root, position).map(|found| (found.open.start(), found.close.start()))
    }

    /// With the caret at each `|` in turn: the pair, as offsets into the
    /// text with the carets taken out.
    fn at_each(marked: &str) -> Vec<Option<(u32, u32)>> {
        let text = marked.replace('|', "");
        let root = rustlyn_syntax::parse(SourceText::new("A.cs", text.as_str())).root();
        marked
            .match_indices('|')
            .enumerate()
            .map(|(index, (at, _))| {
                let position = (at - index) as u32;
                matching_braces(&root, position)
                    .map(|found| (found.open.start(), found.close.start()))
            })
            .collect()
    }

    #[test]
    fn braces_parentheses_and_brackets() {
        let text = "class C { void M(int a) { var x = a[(1 + 2)]; } }";
        let first = |needle: &str| text.find(needle).expect("in the text") as u32;
        let last = |needle: &str| text.rfind(needle).expect("in the text") as u32;
        let class = Some((first("{"), last("}")));
        // Before the opening brace, after the closing one, and just inside
        // either.
        assert_eq!(
            at_each("class C |{| void M(int a) { var x = a[(1 + 2)]; } |}|"),
            [class, class, class, class]
        );
        assert_eq!(
            offsets("class C { void M|(int a) { var x = a[(1 + 2)]; } }"),
            Some((first("("), first(")")))
        );
        assert_eq!(
            offsets("class C { void M(int a) { var x = a|[(1 + 2)]; } }"),
            Some((first("["), first("]")))
        );
        // Between two brackets, the one on the right wins.
        assert_eq!(
            offsets("class C { void M(int a) { var x = a[|(1 + 2)]; } }"),
            Some((first("(1"), first(")]")))
        );
        assert_eq!(
            offsets("class C { void M(int a) { var x = a[(1 + 2)|]; } }"),
            Some((first("["), first("]")))
        );
        assert_eq!(
            offsets("class C { void M(int a) { var x = a[(1 + 2)]; }| }"),
            Some((first("{ var"), last("} }")))
        );
        assert_eq!(offsets("class C { void| M(int a) { } }"), None);
    }

    #[test]
    fn angle_brackets_only_of_generics() {
        let text = "class C { List<Dictionary<int, string>> x; }";
        let first = |needle: &str| text.find(needle).expect("in the text") as u32;
        assert_eq!(
            pair("class C { List|<Dictionary<int, string>> x; }"),
            Some(("<".to_owned(), ">".to_owned()))
        );
        assert_eq!(
            offsets("class C { List|<Dictionary<int, string>> x; }"),
            Some((first("<D"), first("> x")))
        );
        assert_eq!(
            offsets("class C { List<Dictionary|<int, string>> x; }"),
            Some((first("<int"), first(">>")))
        );
        assert_eq!(offsets("class C<T|> { }"), Some((7, 9)));
        assert_eq!(offsets("class C { bool b = a |< b; }"), None);
        assert_eq!(offsets("class C { bool b = a > b|; }"), None);
    }

    #[test]
    fn quotes_of_literals_and_interpolations() {
        assert_eq!(
            pair("class C { string s = |\"text\"; }"),
            Some(("\"".to_owned(), "\"".to_owned()))
        );
        assert_eq!(
            pair("class C { string s = @\"text\"|; }"),
            Some(("@\"".to_owned(), "\"".to_owned()))
        );
        assert_eq!(
            pair("class C { string s = |\"\"\"raw\"\"\"; }"),
            Some(("\"\"\"".to_owned(), "\"\"\"".to_owned()))
        );
        assert_eq!(
            pair("class C { char c = |'x'; }"),
            Some(("'".to_owned(), "'".to_owned()))
        );
        assert_eq!(
            pair("class C { var s = |\"a\"u8; }"),
            Some(("\"".to_owned(), "\"u8".to_owned()))
        );
        assert_eq!(
            pair("class C { string s = |$\"a{b}c\"; }"),
            Some(("$\"".to_owned(), "\"".to_owned()))
        );
        assert_eq!(
            offsets("class C { string s = $\"a|{b}c\"; }"),
            Some((24, 26))
        );
    }

    #[test]
    fn directives_match_along_their_chain() {
        let text = "class C\n{\n#if A\n    int a;\n#elif B\n    int b;\n#else\n    int c;\n#endif\n    #region Names\n    #region Inner\n    #endregion\n    #endregion\n}\n";
        let at = |needle: &str| text.find(needle).expect("the directive") as u32;
        let root = rustlyn_syntax::parse(SourceText::new("A.cs", text)).root();
        let pair = |position: u32| {
            matching_braces(&root, position).map(|found| (found.open.start(), found.close.start()))
        };
        assert_eq!(pair(at("#if")), Some((at("#if"), at("#elif"))));
        assert_eq!(pair(at("#elif")), Some((at("#elif"), at("#else"))));
        assert_eq!(pair(at("#else") + 5), Some((at("#else"), at("#endif"))));
        assert_eq!(pair(at("#endif")), Some((at("#if"), at("#endif"))));
        let outer = at("#region Names");
        let inner = at("#region Inner");
        let inner_end = at("#endregion");
        let outer_end = text.rfind("#endregion").expect("the last") as u32;
        assert_eq!(pair(outer), Some((outer, outer_end)));
        assert_eq!(pair(inner + 7), Some((inner, inner_end)));
        assert_eq!(pair(outer_end), Some((outer, outer_end)));
    }
}
