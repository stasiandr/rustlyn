//! Keyword highlighting: with the cursor on a keyword, the other keywords of
//! the same construct.
//!
//! This is Roslyn's set of keyword highlighters, and like them it reads the
//! syntax only: which `else` belongs to which `if`, which `break` leaves
//! which loop, which `return` returns from which method are all settled by
//! the shape of the tree. A nested lambda or local function is a method of
//! its own, so its `return`s and `await`s are not the outer one's; a nested
//! loop has its own `break`s, and a `switch` inside a loop takes the
//! `break`s but not the `continue`s.

use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

/// The spans to highlight for the cursor at `offset` of the file `root`, or
/// `None` when the cursor is not on a keyword this knows, nor in an `#if` or
/// `#region` directive.
#[must_use]
pub fn keyword_highlights(root: &SyntaxNode, offset: u32) -> Option<Vec<TextSpan>> {
    if let Some(spans) = directive_highlights(root, offset) {
        return Some(spans);
    }
    let token = keyword_at(root, offset)?;
    let parent = token.parent().clone();
    let spans = match token.kind() {
        SyntaxKind::IfKeyword | SyntaxKind::ElseKeyword => if_chain(&token)?,
        SyntaxKind::ForKeyword
        | SyntaxKind::ForEachKeyword
        | SyntaxKind::DoKeyword
        | SyntaxKind::WhileKeyword
            if is_loop(parent.kind()) =>
        {
            loop_highlights(&parent)
        }
        SyntaxKind::BreakKeyword if parent.kind() == SyntaxKind::BreakStatement => {
            let owner = parent
                .ancestors()
                .take_while(|ancestor| !is_function(ancestor.kind()))
                .find(|ancestor| {
                    is_loop(ancestor.kind()) || ancestor.kind() == SyntaxKind::SwitchStatement
                })?;
            if owner.kind() == SyntaxKind::SwitchStatement {
                switch_highlights(&owner)
            } else {
                loop_highlights(&owner)
            }
        }
        SyntaxKind::ContinueKeyword => {
            let owner = parent
                .ancestors()
                .take_while(|ancestor| !is_function(ancestor.kind()))
                .find(|ancestor| is_loop(ancestor.kind()))?;
            loop_highlights(&owner)
        }
        SyntaxKind::SwitchKeyword if parent.kind() == SyntaxKind::SwitchStatement => {
            switch_highlights(&parent)
        }
        SyntaxKind::CaseKeyword | SyntaxKind::DefaultKeyword
            if matches!(
                parent.kind(),
                SyntaxKind::CaseSwitchLabel
                    | SyntaxKind::CasePatternSwitchLabel
                    | SyntaxKind::DefaultSwitchLabel
                    | SyntaxKind::GotoCaseStatement
                    | SyntaxKind::GotoDefaultStatement
            ) =>
        {
            let owner = parent
                .ancestors()
                .find(|ancestor| ancestor.kind() == SyntaxKind::SwitchStatement)?;
            switch_highlights(&owner)
        }
        SyntaxKind::ReturnKeyword | SyntaxKind::YieldKeyword | SyntaxKind::BreakKeyword
            if matches!(
                parent.kind(),
                SyntaxKind::ReturnStatement
                    | SyntaxKind::YieldReturnStatement
                    | SyntaxKind::YieldBreakStatement
            ) =>
        {
            let function = parent
                .ancestors()
                .find(|ancestor| is_function(ancestor.kind()))?;
            return_highlights(&function)
        }
        SyntaxKind::TryKeyword | SyntaxKind::CatchKeyword | SyntaxKind::FinallyKeyword => {
            let statement = std::iter::once(parent.clone())
                .chain(parent.ancestors())
                .find(|ancestor| ancestor.kind() == SyntaxKind::TryStatement)?;
            try_highlights(&statement)
        }
        SyntaxKind::AsyncKeyword | SyntaxKind::AwaitKeyword => {
            let function = if token.kind() == SyntaxKind::AsyncKeyword && is_function(parent.kind())
            {
                parent
            } else {
                parent
                    .ancestors()
                    .find(|ancestor| is_function(ancestor.kind()))?
            };
            async_highlights(&function)
        }
        // A construct with one keyword: the keyword is all there is to show.
        SyntaxKind::CheckedKeyword
        | SyntaxKind::UncheckedKeyword
        | SyntaxKind::LockKeyword
        | SyntaxKind::UsingKeyword
        | SyntaxKind::FixedKeyword
        | SyntaxKind::UnsafeKeyword
            if matches!(
                parent.kind(),
                SyntaxKind::CheckedStatement
                    | SyntaxKind::UncheckedStatement
                    | SyntaxKind::CheckedExpression
                    | SyntaxKind::UncheckedExpression
                    | SyntaxKind::LockStatement
                    | SyntaxKind::UsingStatement
                    | SyntaxKind::FixedStatement
                    | SyntaxKind::UnsafeStatement
            ) =>
        {
            vec![token.span()]
        }
        _ => return None,
    };
    (!spans.is_empty()).then_some(spans)
}

/// The keyword at `offset`, or the one ending there.
fn keyword_at(root: &SyntaxNode, offset: u32) -> Option<SyntaxToken> {
    let is_keyword = |token: &SyntaxToken| token.kind().is_any_keyword();
    root.find_token(offset)
        .filter(|token| token.span().contains(offset) && is_keyword(token))
        .or_else(|| {
            let before = root.find_token(offset.checked_sub(1)?)?;
            (before.span().end() == offset && is_keyword(&before)).then_some(before)
        })
}

const fn is_loop(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::ForStatement
            | SyntaxKind::ForEachStatement
            | SyntaxKind::ForEachVariableStatement
            | SyntaxKind::WhileStatement
            | SyntaxKind::DoStatement
    )
}

/// Whether a node is something `return` returns from.
const fn is_function(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::MethodDeclaration
            | SyntaxKind::ConstructorDeclaration
            | SyntaxKind::DestructorDeclaration
            | SyntaxKind::OperatorDeclaration
            | SyntaxKind::ConversionOperatorDeclaration
            | SyntaxKind::GetAccessorDeclaration
            | SyntaxKind::SetAccessorDeclaration
            | SyntaxKind::InitAccessorDeclaration
            | SyntaxKind::AddAccessorDeclaration
            | SyntaxKind::RemoveAccessorDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::IndexerDeclaration
            | SyntaxKind::LocalFunctionStatement
            | SyntaxKind::SimpleLambdaExpression
            | SyntaxKind::ParenthesizedLambdaExpression
            | SyntaxKind::AnonymousMethodExpression
            | SyntaxKind::CompilationUnit
    )
}

/// Every node under `node` that `keep` accepts, not looking inside the ones
/// `stop` refuses to enter.
fn collect(
    node: &SyntaxNode,
    stop: &dyn Fn(&SyntaxNode) -> bool,
    keep: &mut dyn FnMut(&SyntaxNode),
) {
    for child in node.children() {
        keep(&child);
        if !stop(&child) {
            collect(&child, stop, keep);
        }
    }
}

fn keyword(node: &SyntaxNode, kind: SyntaxKind) -> Option<TextSpan> {
    node.child_token_of_kind(kind).map(|token| token.span())
}

/// A statement's keyword through its semicolon: `break;`, `continue;`.
fn through_semicolon(statement: &SyntaxNode) -> TextSpan {
    let span = statement.span();
    TextSpan::from_bounds(
        statement
            .first_token()
            .map_or(span.start(), |token| token.span().start()),
        span.end(),
    )
}

/// `if`, and every `else` and `else if` after it. `else if` on one line is
/// one span.
fn if_chain(token: &SyntaxToken) -> Option<Vec<TextSpan>> {
    let mut statement = match token.parent().kind() {
        SyntaxKind::IfStatement => token.parent().clone(),
        SyntaxKind::ElseClause => token.parent().parent()?.clone(),
        _ => return None,
    };
    // Up to the first `if` of the chain.
    while let Some(clause) = statement.parent()
        && clause.kind() == SyntaxKind::ElseClause
        && let Some(outer) = clause.parent()
        && outer.kind() == SyntaxKind::IfStatement
    {
        statement = outer.clone();
    }
    let mut spans = Vec::new();
    let mut pending_else: Option<SyntaxToken> = None;
    loop {
        let if_keyword = statement.child_token_of_kind(SyntaxKind::IfKeyword)?;
        match pending_else.take() {
            Some(else_keyword) if on_one_line(&else_keyword, &if_keyword) => {
                spans.push(TextSpan::from_bounds(
                    else_keyword.span().start(),
                    if_keyword.span().end(),
                ));
            }
            Some(else_keyword) => {
                spans.push(else_keyword.span());
                spans.push(if_keyword.span());
            }
            None => spans.push(if_keyword.span()),
        }
        let Some(clause) = statement.child_of_kind(SyntaxKind::ElseClause) else {
            break;
        };
        let else_keyword = clause.child_token_of_kind(SyntaxKind::ElseKeyword)?;
        match clause.child_of_kind(SyntaxKind::IfStatement) {
            Some(next) => {
                pending_else = Some(else_keyword);
                statement = next;
            }
            None => {
                spans.push(else_keyword.span());
                break;
            }
        }
    }
    Some(spans)
}

/// Whether nothing but spaces stands between two tokens.
fn on_one_line(first: &SyntaxToken, second: &SyntaxToken) -> bool {
    first
        .trailing_trivia()
        .iter()
        .chain(second.leading_trivia().iter())
        .all(|trivia| trivia.kind() == SyntaxKind::WhitespaceTrivia)
}

/// A loop's keywords, and the `break`s and `continue`s that leave or restart
/// it.
fn loop_highlights(statement: &SyntaxNode) -> Vec<TextSpan> {
    let mut spans = Vec::new();
    match statement.kind() {
        SyntaxKind::DoStatement => {
            spans.extend(keyword(statement, SyntaxKind::DoKeyword));
            spans.extend(keyword(statement, SyntaxKind::WhileKeyword));
        }
        SyntaxKind::ForStatement => spans.extend(keyword(statement, SyntaxKind::ForKeyword)),
        SyntaxKind::WhileStatement => spans.extend(keyword(statement, SyntaxKind::WhileKeyword)),
        _ => spans.extend(keyword(statement, SyntaxKind::ForEachKeyword)),
    }
    loop_exits(statement, false, &mut spans);
    spans.sort_by_key(|span| span.start());
    spans
}

fn loop_exits(node: &SyntaxNode, in_switch: bool, spans: &mut Vec<TextSpan>) {
    for child in node.children() {
        match child.kind() {
            kind if is_loop(kind) || is_function(kind) => {}
            SyntaxKind::SwitchStatement => loop_exits(&child, true, spans),
            SyntaxKind::BreakStatement if !in_switch => spans.push(through_semicolon(&child)),
            SyntaxKind::ContinueStatement => spans.push(through_semicolon(&child)),
            _ => loop_exits(&child, in_switch, spans),
        }
    }
}

/// A `switch`, its `case` and `default` labels, its `break`s and the
/// `goto case`s that jump within it.
fn switch_highlights(statement: &SyntaxNode) -> Vec<TextSpan> {
    let mut spans: Vec<TextSpan> = keyword(statement, SyntaxKind::SwitchKeyword)
        .into_iter()
        .collect();
    for section in statement
        .children()
        .filter(|child| child.kind() == SyntaxKind::SwitchSection)
    {
        for label in section.children() {
            match label.kind() {
                SyntaxKind::CaseSwitchLabel | SyntaxKind::CasePatternSwitchLabel => {
                    spans.extend(keyword(&label, SyntaxKind::CaseKeyword));
                }
                SyntaxKind::DefaultSwitchLabel => {
                    spans.extend(keyword(&label, SyntaxKind::DefaultKeyword));
                }
                _ => {}
            }
        }
        collect(
            &section,
            &|node| {
                is_loop(node.kind())
                    || is_function(node.kind())
                    || node.kind() == SyntaxKind::SwitchStatement
            },
            &mut |node| match node.kind() {
                SyntaxKind::BreakStatement
                    if !node
                        .ancestors()
                        .take_while(|ancestor| ancestor != statement)
                        .any(|ancestor| is_loop(ancestor.kind())) =>
                {
                    spans.push(through_semicolon(node));
                }
                SyntaxKind::GotoCaseStatement | SyntaxKind::GotoDefaultStatement => {
                    if let (Some(goto), Some(label)) = (
                        node.child_token_of_kind(SyntaxKind::GotoKeyword),
                        node.child_token_of_kind(SyntaxKind::CaseKeyword)
                            .or_else(|| node.child_token_of_kind(SyntaxKind::DefaultKeyword)),
                    ) {
                        spans.push(TextSpan::from_bounds(
                            goto.span().start(),
                            label.span().end(),
                        ));
                    }
                }
                _ => {}
            },
        );
    }
    spans.sort_by_key(|span| span.start());
    spans
}

/// Every `return`, `yield return` and `yield break` of a method, lambda or
/// local function — not those of one nested in it.
fn return_highlights(function: &SyntaxNode) -> Vec<TextSpan> {
    let mut spans = Vec::new();
    collect(
        function,
        &|node| is_function(node.kind()),
        &mut |node| match node.kind() {
            SyntaxKind::ReturnStatement => {
                spans.extend(keyword(node, SyntaxKind::ReturnKeyword));
            }
            SyntaxKind::YieldReturnStatement | SyntaxKind::YieldBreakStatement => {
                if let (Some(yield_keyword), Some(last)) = (
                    node.child_token_of_kind(SyntaxKind::YieldKeyword),
                    node.child_token_of_kind(SyntaxKind::ReturnKeyword)
                        .or_else(|| node.child_token_of_kind(SyntaxKind::BreakKeyword)),
                ) {
                    spans.push(TextSpan::from_bounds(
                        yield_keyword.span().start(),
                        last.span().end(),
                    ));
                }
            }
            _ => {}
        },
    );
    spans
}

/// `try`, each `catch` and the `finally`.
fn try_highlights(statement: &SyntaxNode) -> Vec<TextSpan> {
    let mut spans: Vec<TextSpan> = keyword(statement, SyntaxKind::TryKeyword)
        .into_iter()
        .collect();
    for clause in statement.children() {
        match clause.kind() {
            SyntaxKind::CatchClause => spans.extend(keyword(&clause, SyntaxKind::CatchKeyword)),
            SyntaxKind::FinallyClause => {
                spans.extend(keyword(&clause, SyntaxKind::FinallyKeyword));
            }
            _ => {}
        }
    }
    spans
}

/// A function's `async`, and every `await` in it that is not in a function
/// nested inside.
fn async_highlights(function: &SyntaxNode) -> Vec<TextSpan> {
    let mut spans: Vec<TextSpan> = keyword(function, SyntaxKind::AsyncKeyword)
        .into_iter()
        .collect();
    collect(function, &|node| is_function(node.kind()), &mut |node| {
        if !is_function(node.kind()) {
            spans.extend(keyword(node, SyntaxKind::AwaitKeyword));
        }
    });
    spans.sort_by_key(|span| span.start());
    spans
}

/// With the cursor in an `#if`, `#elif`, `#else` or `#endif`, every
/// directive of that group; in a `#region` or `#endregion`, the pair.
fn directive_highlights(root: &SyntaxNode, offset: u32) -> Option<Vec<TextSpan>> {
    // Cheap first: is the cursor in a directive at all?
    let token = root.find_token(offset)?;
    let inside = token
        .leading_trivia()
        .into_iter()
        .chain(token.trailing_trivia())
        .find(|trivia| {
            is_grouping_directive(trivia.kind())
                && (trivia.span().contains(offset) || trivia.span().end() == offset)
        })?;

    let conditional = matches!(
        inside.kind(),
        SyntaxKind::IfDirectiveTrivia
            | SyntaxKind::ElifDirectiveTrivia
            | SyntaxKind::ElseDirectiveTrivia
            | SyntaxKind::EndIfDirectiveTrivia
    );
    // Every group, matched the way the preprocessor matches them.
    let mut open: Vec<Vec<TextSpan>> = Vec::new();
    let mut groups: Vec<Vec<TextSpan>> = Vec::new();
    for token in root.descendant_tokens() {
        if token.full_span() == token.span() {
            continue;
        }
        for trivia in token
            .leading_trivia()
            .into_iter()
            .chain(token.trailing_trivia())
        {
            let kind = trivia.kind();
            let span = directive_keyword(trivia.span(), trivia.text());
            match kind {
                SyntaxKind::IfDirectiveTrivia if conditional => open.push(vec![span]),
                SyntaxKind::RegionDirectiveTrivia if !conditional => open.push(vec![span]),
                SyntaxKind::ElifDirectiveTrivia | SyntaxKind::ElseDirectiveTrivia
                    if conditional =>
                {
                    if let Some(group) = open.last_mut() {
                        group.push(span);
                    }
                }
                SyntaxKind::EndIfDirectiveTrivia if conditional => {
                    if let Some(mut group) = open.pop() {
                        group.push(span);
                        groups.push(group);
                    }
                }
                SyntaxKind::EndRegionDirectiveTrivia if !conditional => {
                    if let Some(mut group) = open.pop() {
                        group.push(span);
                        groups.push(group);
                    }
                }
                _ => {}
            }
        }
    }
    // A group left open at the end of the file is still a group.
    groups.extend(open);
    let at = directive_keyword(inside.span(), inside.text());
    groups.into_iter().find(|group| group.contains(&at))
}

const fn is_grouping_directive(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::IfDirectiveTrivia
            | SyntaxKind::ElifDirectiveTrivia
            | SyntaxKind::ElseDirectiveTrivia
            | SyntaxKind::EndIfDirectiveTrivia
            | SyntaxKind::RegionDirectiveTrivia
            | SyntaxKind::EndRegionDirectiveTrivia
    )
}

/// The `#` of a directive through the end of its keyword: `#if` of
/// `#if DEBUG`, `# endregion` of `# endregion Setup`.
fn directive_keyword(span: TextSpan, text: &str) -> TextSpan {
    let bytes = text.as_bytes();
    let mut end = text.find('#').map_or(0, |at| at + 1);
    while end < bytes.len() && (bytes[end] == b' ' || bytes[end] == b'\t') {
        end += 1;
    }
    while end < bytes.len() && bytes[end].is_ascii_alphabetic() {
        end += 1;
    }
    let start = text.find('#').unwrap_or(0);
    TextSpan::from_bounds(span.start() + start as u32, span.start() + end as u32)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustlyn_text::SourceText;

    /// The text of each span highlighted with the cursor `into` bytes into
    /// the first `marker`.
    fn highlighted(text: &str, marker: &str, into: usize) -> Vec<String> {
        let tree = rustlyn_syntax::parse(SourceText::new("a.cs", text));
        let offset = (text.find(marker).expect("the marker") + into) as u32;
        keyword_highlights(&tree.root(), offset)
            .unwrap_or_default()
            .into_iter()
            .map(|span| text[span.start() as usize..span.end() as usize].to_string())
            .collect()
    }

    #[test]
    fn an_if_chain_from_any_of_its_keywords() {
        let text = "class C { void M(int x) {\n if (x > 0) { }\n else if (x < 0) { }\n else\n  if (x == 5) { }\n  else { }\n} }\n";
        let expected = vec!["if", "else if", "else", "if", "else"];
        assert_eq!(highlighted(text, "if (x > 0)", 0), expected);
        assert_eq!(highlighted(text, "else if", 0), expected);
        assert_eq!(highlighted(text, "else { }", 2), expected);
    }

    #[test]
    fn a_loop_with_its_breaks_and_continues_but_not_a_nested_ones() {
        let text = "class C { void M(int[] xs) {\n foreach (var x in xs) {\n  if (x == 0) continue;\n  switch (x) { case 1: break; }\n  for (;;) { break; }\n  if (x > 9) break;\n }\n} }\n";
        assert_eq!(
            highlighted(text, "foreach", 0),
            vec!["foreach", "continue;", "break;"]
        );
        assert_eq!(
            highlighted(text, "continue", 3),
            vec!["foreach", "continue;", "break;"]
        );
        // The `break` inside the switch belongs to the switch.
        assert_eq!(
            highlighted(text, "break; }", 0),
            vec!["switch", "case", "break;"]
        );
        let text = "class C { void M() { do { if (true) break; } while (false); } }\n";
        assert_eq!(highlighted(text, "do", 0), vec!["do", "break;", "while"]);
    }

    #[test]
    fn a_switch_with_its_labels_and_breaks() {
        let text = "class C { void M(int x) {\n switch (x) {\n  case 1: goto case 2;\n  case 2: while (true) { break; } break;\n  default: break;\n }\n} }\n";
        assert_eq!(
            highlighted(text, "switch", 0),
            vec![
                "switch",
                "case",
                "goto case",
                "case",
                "break;",
                "default",
                "break;"
            ]
        );
        assert_eq!(highlighted(text, "default", 0).len(), 7);
    }

    #[test]
    fn returns_of_the_method_and_not_of_its_lambdas() {
        let text = "using System.Collections.Generic;\nclass C {\n IEnumerable<int> M(bool b) {\n  if (b) yield break;\n  System.Func<int> f = () => { return 1; };\n  yield return 2;\n }\n int N(int x) { if (x > 0) return 1; return 0; }\n}\n";
        assert_eq!(
            highlighted(text, "yield break", 0),
            vec!["yield break", "yield return"]
        );
        assert_eq!(highlighted(text, "return 1;", 0), vec!["return"]);
        assert_eq!(highlighted(text, "return 0", 0), vec!["return", "return"]);
    }

    #[test]
    fn try_catch_finally_and_async_await() {
        let text = "class C {\n async System.Threading.Tasks.Task M() {\n  try { await X(); }\n  catch (System.Exception) { }\n  catch { }\n  finally { }\n  System.Func<System.Threading.Tasks.Task> f = async () => await X();\n  await X();\n }\n static System.Threading.Tasks.Task X() => null;\n}\n";
        assert_eq!(
            highlighted(text, "finally", 0),
            vec!["try", "catch", "catch", "finally"]
        );
        assert_eq!(
            highlighted(text, "async System", 0),
            vec!["async", "await", "await"]
        );
        assert_eq!(highlighted(text, "async ()", 0), vec!["async", "await"]);
    }

    #[test]
    fn single_keyword_constructs() {
        let text = "class C { object o; void M() { lock (o) { } checked { } } }\n";
        assert_eq!(highlighted(text, "lock", 0), vec!["lock"]);
        assert_eq!(highlighted(text, "checked", 0), vec!["checked"]);
        assert!(highlighted(text, "void", 0).is_empty());
    }

    #[test]
    fn directives_are_matched_as_the_preprocessor_matches_them() {
        let text = "class C {\n#region Fields\n#if !DEBUG\n int a;\n#if TRACE\n int t;\n#endif\n#elif RELEASE\n int b;\n#else\n int c;\n#endif\n#endregion\n}\n";
        assert_eq!(
            highlighted(text, "#elif", 1),
            vec!["#if", "#elif", "#else", "#endif"]
        );
        assert_eq!(highlighted(text, "#if TRACE", 1), vec!["#if", "#endif"]);
        assert_eq!(
            highlighted(text, "#endregion", 3),
            vec!["#region", "#endregion"]
        );
    }
}
