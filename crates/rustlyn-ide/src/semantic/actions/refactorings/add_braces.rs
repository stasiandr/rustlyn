//! Add braces: put the one statement an `if`, `else`, loop, `using`,
//! `lock` or `fixed` controls into a block.
//!
//! Roslyn offers this as the fix for IDE0011; with the cursor on the
//! statement that controls it, it is here too. The block is laid out the
//! way the file lays out blocks, on lines of their own. An `else if` is
//! left alone: the `if` is the `else`'s statement, and bracing it would
//! only indent the chain.

use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::super::text::{is_statement, reindent, starts_line};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(token) = context.token_at_cursor() else {
        return;
    };
    let Some(owner) = std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .find(|node| controls(node).is_some())
    else {
        return;
    };
    let Some(embedded) = controls(&owner) else {
        return;
    };
    // The header only: the cursor inside the embedded statement is about
    // that statement.
    if context.trimmed_span().start() >= embedded.span().start() {
        return;
    }
    if embedded.kind() == SyntaxKind::Block
        || (owner.kind() == SyntaxKind::ElseClause && embedded.kind() == SyntaxKind::IfStatement)
    {
        return;
    }
    let Some(start) = header_end(&owner, &embedded) else {
        return;
    };
    let indent = context.indentation_at(owner.span().start());
    let unit = context.indent_unit();
    let newline = context.newline();
    let inner = format!("{indent}{unit}");
    let from = if starts_line(&context.text, embedded.span().start()) {
        context.indentation_at(embedded.span().start())
    } else {
        // On the header's own line: its continuation lines are indented
        // from the header.
        inner.clone()
    };
    let statement = reindent(&embedded.text(), &from, &inner);
    let mut text = format!("{newline}{indent}{{{newline}{inner}{statement}{newline}{indent}}}");
    let mut end = embedded.span().end();
    if owner.kind() == SyntaxKind::DoStatement {
        // `while (...)` follows on its own line.
        let Some(keyword) = owner.child_token_of_kind(SyntaxKind::WhileKeyword) else {
            return;
        };
        text.push_str(newline);
        text.push_str(&indent);
        end = keyword.span().start();
    }
    found.push(context.local(
        "Add braces",
        ActionKind::Rewrite,
        None,
        vec![TextEdit::new(TextSpan::from_bounds(start, end), text)],
    ));
}

/// The statement `node` controls, for the statements that control one.
fn controls(node: &SyntaxNode) -> Option<SyntaxNode> {
    use SyntaxKind as K;
    match node.kind() {
        K::IfStatement
        | K::ElseClause
        | K::WhileStatement
        | K::DoStatement
        | K::ForStatement
        | K::ForEachStatement
        | K::ForEachVariableStatement
        | K::UsingStatement
        | K::LockStatement
        | K::FixedStatement => node.children().find(|child| is_statement(child.kind())),
        _ => None,
    }
}

/// Where the header before `embedded` ends: after its `)`, or after `else`
/// or `do`.
fn header_end(owner: &SyntaxNode, embedded: &SyntaxNode) -> Option<u32> {
    owner
        .child_tokens()
        .filter(|token| token.span().end() <= embedded.span().start())
        .last()
        .map(|token| token.span().end())
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn an_if_and_its_else_get_blocks() {
        let source = "class C\n{\n    void M(bool b)\n    {\n        $$if (b) M(false);\n        else M(true);\n    }\n}\n";
        assert_eq!(
            apply(source, "Add braces"),
            "class C\n{\n    void M(bool b)\n    {\n        if (b)\n        {\n            M(false);\n        }\n        else M(true);\n    }\n}\n"
        );
        let other = "class C\n{\n    void M(bool b)\n    {\n        if (b) M(false);\n        el$$se M(true);\n    }\n}\n";
        assert_eq!(
            apply(other, "Add braces"),
            "class C\n{\n    void M(bool b)\n    {\n        if (b) M(false);\n        else\n        {\n            M(true);\n        }\n    }\n}\n"
        );
    }

    #[test]
    fn a_loop_on_two_lines_keeps_its_statement() {
        let source = "class C\n{\n    void M(int[] items)\n    {\n        for$$each (var item in items)\n            System.Console.WriteLine(item);\n    }\n}\n";
        assert_eq!(
            apply(source, "Add braces"),
            "class C\n{\n    void M(int[] items)\n    {\n        foreach (var item in items)\n        {\n            System.Console.WriteLine(item);\n        }\n    }\n}\n"
        );
    }

    #[test]
    fn a_do_loop_keeps_its_while() {
        let source =
            "class C\n{\n    void M(int n)\n    {\n        $$do n--; while (n > 0);\n    }\n}\n";
        assert_eq!(
            apply(source, "Add braces"),
            "class C\n{\n    void M(int n)\n    {\n        do\n        {\n            n--;\n        }\n        while (n > 0);\n    }\n}\n"
        );
    }

    #[test]
    fn a_block_or_an_else_if_is_left_alone() {
        refuses(
            "class C\n{\n    void M(bool b)\n    {\n        $$if (b) { M(false); }\n    }\n}\n",
            "Add braces",
        );
        refuses(
            "class C\n{\n    void M(bool b)\n    {\n        if (b) { }\n        el$$se if (!b) { }\n    }\n}\n",
            "Add braces",
        );
    }
}
