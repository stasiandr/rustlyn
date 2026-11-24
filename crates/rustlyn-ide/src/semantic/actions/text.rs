//! What every provider needs to write code that looks like the code around
//! it: the file's line ending and indentation, a type spelled the way the
//! file would spell it, a name nothing in scope already has, and parentheses
//! exactly where an expression moved somewhere else needs them.
//!
//! Roslyn builds syntax trees and lets a formatter lay them out. There is no
//! formatter here, so providers write text; these are the pieces that keep
//! that text in the file's own style — an edit that reads like a stranger
//! wrote it is one the user has to fix by hand.

use std::collections::HashSet;

use rustlyn_semantics::{SpecialType, SymbolId, SymbolKind, Type};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::Context;
use crate::semantic::View;

// MARK: - lines

/// The line ending the file uses: `\r\n` when it has any, `\n` otherwise.
pub(crate) fn newline(text: &str) -> &'static str {
    if text.contains("\r\n") { "\r\n" } else { "\n" }
}

/// Where the line holding `offset` starts.
pub(crate) fn line_start(text: &str, offset: u32) -> u32 {
    let offset = (offset as usize).min(text.len());
    text[..offset].rfind('\n').map_or(0, |at| at as u32 + 1)
}

/// Where the line holding `offset` ends: at its line break, which is not
/// part of it.
pub(crate) fn line_end(text: &str, offset: u32) -> u32 {
    let offset = (offset as usize).min(text.len());
    let end = text[offset..]
        .find('\n')
        .map_or(text.len(), |at| offset + at);
    if end > 0 && text.as_bytes()[end - 1] == b'\r' && end > offset {
        (end - 1) as u32
    } else {
        end as u32
    }
}

/// The whitespace a line starts with, for the line holding `offset`.
pub(crate) fn indentation_at(text: &str, offset: u32) -> String {
    let start = line_start(text, offset) as usize;
    text[start..]
        .chars()
        .take_while(|c| *c == ' ' || *c == '\t')
        .collect()
}

/// Whether only whitespace comes before `offset` on its line.
pub(crate) fn starts_line(text: &str, offset: u32) -> bool {
    let start = line_start(text, offset);
    text[start as usize..offset as usize].trim().is_empty()
}

/// One level of indentation as the file writes it: a tab when its lines are
/// indented with tabs, otherwise the step between one level and the next
/// that occurs most often, and four spaces when the file does not say.
pub(crate) fn indent_unit(text: &str) -> String {
    let mut steps: std::collections::HashMap<usize, usize> = std::collections::HashMap::new();
    let mut previous = 0usize;
    for line in text.lines() {
        if line.trim().is_empty() {
            continue;
        }
        if line.starts_with('\t') {
            return "\t".to_string();
        }
        let width = line.len() - line.trim_start_matches(' ').len();
        if width > previous {
            *steps.entry(width - previous).or_default() += 1;
        }
        previous = width;
    }
    let step = steps
        .into_iter()
        .max_by_key(|&(step, count)| (count, std::cmp::Reverse(step)))
        .map_or(4, |(step, _)| step);
    " ".repeat(step)
}

/// `snippet` moved from lines indented with `from` to lines indented with
/// `to`. The first line is left alone — it starts wherever the snippet is
/// put — and a line that does not start with `from` keeps what it has,
/// since there is no way to say what its indentation was relative to.
pub(crate) fn reindent(snippet: &str, from: &str, to: &str) -> String {
    let mut out = String::with_capacity(snippet.len());
    for (index, line) in snippet.split('\n').enumerate() {
        if index > 0 {
            out.push('\n');
            if line.trim().is_empty() {
                // Keep a `\r` so a `\r\n` file keeps its endings.
                if line.ends_with('\r') {
                    out.push('\r');
                }
                continue;
            }
            if let Some(rest) = line.strip_prefix(from) {
                out.push_str(to);
                out.push_str(rest);
                continue;
            }
        }
        out.push_str(line);
    }
    out
}

/// `span` grown to the whole lines it is on, line break included, when
/// nothing but whitespace shares those lines with it: what removing a
/// statement or a member removes. Otherwise `span` as it is.
pub(crate) fn whole_lines(text: &str, span: TextSpan) -> TextSpan {
    let start = line_start(text, span.start());
    let end = line_end(text, span.end());
    let before = &text[start as usize..span.start() as usize];
    let after = &text[span.end() as usize..end as usize];
    if !before.trim().is_empty() || !after.trim().is_empty() {
        return span;
    }
    let mut end = end as usize;
    if text[end..].starts_with("\r\n") {
        end += 2;
    } else if text[end..].starts_with('\n') {
        end += 1;
    }
    TextSpan::from_bounds(start, end as u32)
}

/// What removing a declaration at `span` removes: its whole lines, and the
/// blank line after it when there is nothing but a blank line or an opening
/// brace before it either — so that removing the first of two members does
/// not leave the blank line that separated them hanging under the brace.
pub(crate) fn declaration_lines(text: &str, span: TextSpan) -> TextSpan {
    let lines = whole_lines(text, span);
    if lines == span {
        return span;
    }
    let before = text[..lines.start() as usize].trim_end_matches([' ', '\t']);
    let before = before.strip_suffix('\n').unwrap_or(before);
    let before = before.strip_suffix('\r').unwrap_or(before);
    let previous_line = &before[line_start(before, before.len() as u32) as usize..];
    let gap_before = previous_line.trim().is_empty() || previous_line.trim_end().ends_with('{');
    let rest = &text[lines.end() as usize..];
    let next_line_end = rest.find('\n').map(|at| at + 1);
    match next_line_end {
        Some(end) if gap_before && rest[..end].trim().is_empty() => {
            TextSpan::from_bounds(lines.start(), lines.end() + end as u32)
        }
        _ => lines,
    }
}

/// The text of `span`.
pub(crate) fn slice(text: &str, span: TextSpan) -> &str {
    text.get(span.start() as usize..span.end() as usize)
        .unwrap_or_default()
}

/// Whether anything inside `node`, between its first and last token, is a
/// comment or a directive: text a rewrite that rebuilds the node would
/// lose.
pub(crate) fn has_comments(node: &SyntaxNode) -> bool {
    let tokens: Vec<SyntaxToken> = node.descendant_tokens().collect();
    let last = tokens.len().saturating_sub(1);
    tokens.iter().enumerate().any(|(index, token)| {
        let leading = if index == 0 {
            Vec::new()
        } else {
            token.leading_trivia()
        };
        let trailing = if index == last {
            Vec::new()
        } else {
            token.trailing_trivia()
        };
        leading
            .iter()
            .chain(trailing.iter())
            .any(|trivia| !is_blank_trivia(trivia.kind()))
    })
}

fn is_blank_trivia(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::WhitespaceTrivia | SyntaxKind::EndOfLineTrivia
    )
}

// MARK: - names

/// `base`, or `base` with the first number after it that makes a name
/// `taken` does not hold: `NewMethod`, `NewMethod1`, `NewMethod2`.
pub(crate) fn fresh_name(base: &str, taken: &HashSet<String>) -> String {
    if !taken.contains(base) && !is_keyword(base) {
        return base.to_string();
    }
    (1..)
        .map(|number| format!("{base}{number}"))
        .find(|name| !taken.contains(name))
        .expect("some number is free")
}

/// Whether `name` is a reserved word, which a name has to avoid.
pub(crate) fn is_keyword(name: &str) -> bool {
    rustlyn_syntax::reserved_keyword_kind(name).is_some()
}

/// Whether `name` is written the way C# spells an identifier.
pub(crate) fn is_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    chars
        .next()
        .is_some_and(|first| first == '_' || first.is_alphabetic())
        && chars.all(|c| c == '_' || c.is_alphanumeric())
        && !is_keyword(name)
}

/// `Name` as a local or parameter would be called: `name`. A leading
/// underscore or `m_` goes, as it does for a field turned into a parameter.
pub(crate) fn camel_case(name: &str) -> String {
    let trimmed = name.strip_prefix("m_").unwrap_or(name);
    let trimmed = trimmed.trim_start_matches('_');
    let trimmed = if trimmed.is_empty() { name } else { trimmed };
    let mut chars = trimmed.chars();
    let Some(first) = chars.next() else {
        return String::new();
    };
    let mut out: String = first.to_lowercase().collect();
    out.push_str(chars.as_str());
    if is_keyword(&out) {
        out.insert(0, '@');
    }
    out
}

/// `name` as a property or a constant would be called: `Name`.
pub(crate) fn pascal_case(name: &str) -> String {
    let trimmed = name.strip_prefix("m_").unwrap_or(name);
    let trimmed = trimmed.trim_start_matches('_').trim_start_matches('@');
    let mut chars = trimmed.chars();
    let Some(first) = chars.next() else {
        return String::new();
    };
    let mut out: String = first.to_uppercase().collect();
    out.push_str(chars.as_str());
    out
}

// MARK: - precedence

/// How tightly an expression of `kind` binds, from 0 (a `throw`) to 18 (a
/// name, a call, a literal): the rows of §12.4.2, which Roslyn's
/// `OperatorPrecedence` follows.
pub(crate) fn precedence(kind: SyntaxKind) -> u8 {
    use SyntaxKind as K;
    match kind {
        K::ThrowExpression => 0,
        K::SimpleAssignmentExpression
        | K::AddAssignmentExpression
        | K::SubtractAssignmentExpression
        | K::MultiplyAssignmentExpression
        | K::DivideAssignmentExpression
        | K::ModuloAssignmentExpression
        | K::AndAssignmentExpression
        | K::ExclusiveOrAssignmentExpression
        | K::OrAssignmentExpression
        | K::LeftShiftAssignmentExpression
        | K::RightShiftAssignmentExpression
        | K::UnsignedRightShiftAssignmentExpression
        | K::CoalesceAssignmentExpression
        | K::SimpleLambdaExpression
        | K::ParenthesizedLambdaExpression
        | K::AnonymousMethodExpression => 1,
        K::ConditionalExpression => 2,
        K::CoalesceExpression => 3,
        K::LogicalOrExpression => 4,
        K::LogicalAndExpression => 5,
        K::BitwiseOrExpression => 6,
        K::ExclusiveOrExpression => 7,
        K::BitwiseAndExpression => 8,
        K::EqualsExpression | K::NotEqualsExpression => 9,
        K::LessThanExpression
        | K::LessThanOrEqualExpression
        | K::GreaterThanExpression
        | K::GreaterThanOrEqualExpression
        | K::IsExpression
        | K::AsExpression
        | K::IsPatternExpression => 10,
        K::LeftShiftExpression | K::RightShiftExpression | K::UnsignedRightShiftExpression => 11,
        K::AddExpression | K::SubtractExpression => 12,
        K::MultiplyExpression | K::DivideExpression | K::ModuloExpression => 13,
        K::WithExpression => 14,
        K::SwitchExpression => 15,
        K::RangeExpression => 16,
        K::UnaryPlusExpression
        | K::UnaryMinusExpression
        | K::BitwiseNotExpression
        | K::LogicalNotExpression
        | K::PreIncrementExpression
        | K::PreDecrementExpression
        | K::CastExpression
        | K::AwaitExpression
        | K::AddressOfExpression
        | K::PointerIndirectionExpression
        | K::IndexExpression
        | K::RefExpression => 17,
        _ => 18,
    }
}

/// Whether an operator of `kind` groups from the right: `a = b = c`,
/// `a ?? b ?? c`, `a ? b : c ? d : e`.
fn is_right_associative(kind: SyntaxKind) -> bool {
    matches!(precedence(kind), 1..=3)
}

/// Whether an expression of `kind`, put where `at` is now, needs
/// parentheses to keep meaning what it meant: `a + b` in place of `x` in
/// `x * 2` does, in place of `x` in `f(x)` does not.
pub(crate) fn needs_parentheses(kind: SyntaxKind, at: &SyntaxNode) -> bool {
    let inner = precedence(kind);
    if inner == 18 {
        return false;
    }
    let Some(parent) = at.parent() else {
        return false;
    };
    let outer_kind = parent.kind();
    if !outer_kind.is_expression() {
        // An argument, an initializer, a statement: nothing binds against
        // it. An interpolation's `:` would be read as a format, though.
        return outer_kind == SyntaxKind::Interpolation
            && kind == SyntaxKind::ConditionalExpression;
    }
    match outer_kind {
        SyntaxKind::ParenthesizedExpression
        | SyntaxKind::TupleExpression
        | SyntaxKind::InterpolatedStringExpression => return false,
        // What is inside the brackets or the argument list of a primary
        // expression is not an operand of it.
        SyntaxKind::ElementAccessExpression | SyntaxKind::InvocationExpression
            if parent.children().next().as_ref() != Some(at) =>
        {
            return false;
        }
        _ => {}
    }
    let outer = precedence(outer_kind);
    if outer == 18 {
        // `(a + b).Length`, `(a + b)[0]`, `(a + b)()`.
        return true;
    }
    if inner != outer {
        return inner < outer;
    }
    // Same row: fine on the side the operator groups from.
    let first = parent.children().next().as_ref() == Some(at);
    if is_right_associative(outer_kind) {
        first
    } else {
        !first
    }
}

/// `text`, an expression of `kind`, in parentheses when put in place of
/// `at` needs them.
pub(crate) fn parenthesized_for(text: &str, kind: SyntaxKind, at: &SyntaxNode) -> String {
    if needs_parentheses(kind, at) {
        format!("({text})")
    } else {
        text.to_string()
    }
}

/// `node` without the parentheses around it.
pub(crate) fn skip_parentheses(node: &SyntaxNode) -> SyntaxNode {
    let mut node = node.clone();
    while node.kind() == SyntaxKind::ParenthesizedExpression {
        match node.children().next() {
            Some(inner) => node = inner,
            None => break,
        }
    }
    node
}

// MARK: - the tree

/// The innermost node that is exactly `span`, trivia aside, climbing out of
/// wrappers that have the same span as what they wrap and keeping the
/// outermost of those that is an expression.
pub(crate) fn node_exactly(root: &SyntaxNode, span: TextSpan) -> Option<SyntaxNode> {
    let node = root.find_node(span)?;
    if node.span() != span {
        return None;
    }
    Some(node)
}

/// The statements a block or switch section holds, in order.
pub(crate) fn statements_of(node: &SyntaxNode) -> Vec<SyntaxNode> {
    node.children()
        .filter(|child| is_statement(child.kind()))
        .collect()
}

/// Whether `kind` is a statement.
pub(crate) fn is_statement(kind: SyntaxKind) -> bool {
    use SyntaxKind as K;
    matches!(
        kind,
        K::Block
            | K::LocalDeclarationStatement
            | K::ExpressionStatement
            | K::EmptyStatement
            | K::LabeledStatement
            | K::GotoStatement
            | K::GotoCaseStatement
            | K::GotoDefaultStatement
            | K::BreakStatement
            | K::ContinueStatement
            | K::ReturnStatement
            | K::YieldReturnStatement
            | K::YieldBreakStatement
            | K::ThrowStatement
            | K::WhileStatement
            | K::DoStatement
            | K::ForStatement
            | K::ForEachStatement
            | K::ForEachVariableStatement
            | K::UsingStatement
            | K::FixedStatement
            | K::CheckedStatement
            | K::UncheckedStatement
            | K::UnsafeStatement
            | K::LockStatement
            | K::IfStatement
            | K::SwitchStatement
            | K::TryStatement
            | K::LocalFunctionStatement
    )
}

/// Whether `kind` declares a member of a type.
pub(crate) fn is_member(kind: SyntaxKind) -> bool {
    use SyntaxKind as K;
    matches!(
        kind,
        K::FieldDeclaration
            | K::EventFieldDeclaration
            | K::MethodDeclaration
            | K::OperatorDeclaration
            | K::ConversionOperatorDeclaration
            | K::ConstructorDeclaration
            | K::DestructorDeclaration
            | K::PropertyDeclaration
            | K::EventDeclaration
            | K::IndexerDeclaration
    ) || is_type_declaration(kind)
}

/// Whether `kind` declares a type with members.
pub(crate) fn is_type_declaration(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::ClassDeclaration
            | SyntaxKind::StructDeclaration
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::RecordDeclaration
            | SyntaxKind::RecordStructDeclaration
    )
}

/// The member of a type that `node` is in: the method, not the type.
pub(crate) fn enclosing_member(node: &SyntaxNode) -> Option<SyntaxNode> {
    std::iter::once(node.clone())
        .chain(node.ancestors())
        .find(|ancestor| {
            is_member(ancestor.kind())
                && !is_type_declaration(ancestor.kind())
                && ancestor
                    .parent()
                    .is_some_and(|parent| is_type_declaration(parent.kind()))
        })
}

/// Whether the name `node` is is being written to: the left of an
/// assignment, the operand of `++` or `--`, or passed by `ref` or `out`.
pub(crate) fn is_written(node: &SyntaxNode) -> bool {
    let mut current = node.clone();
    // `(x) = 1` and `this.x = 1` write `x`.
    while let Some(parent) = current.parent() {
        let climb = match parent.kind() {
            SyntaxKind::ParenthesizedExpression => true,
            SyntaxKind::SimpleMemberAccessExpression => {
                parent.children().last().as_ref() == Some(&current)
                    && parent
                        .children()
                        .next()
                        .is_some_and(|left| left.kind() == SyntaxKind::ThisExpression)
            }
            _ => false,
        };
        if !climb {
            break;
        }
        current = parent.clone();
    }
    let Some(parent) = current.parent() else {
        return false;
    };
    use SyntaxKind as K;
    match parent.kind() {
        K::SimpleAssignmentExpression
        | K::AddAssignmentExpression
        | K::SubtractAssignmentExpression
        | K::MultiplyAssignmentExpression
        | K::DivideAssignmentExpression
        | K::ModuloAssignmentExpression
        | K::AndAssignmentExpression
        | K::ExclusiveOrAssignmentExpression
        | K::OrAssignmentExpression
        | K::LeftShiftAssignmentExpression
        | K::RightShiftAssignmentExpression
        | K::UnsignedRightShiftAssignmentExpression
        | K::CoalesceAssignmentExpression => parent.children().next().as_ref() == Some(&current),
        K::PreIncrementExpression
        | K::PreDecrementExpression
        | K::PostIncrementExpression
        | K::PostDecrementExpression
        | K::AddressOfExpression
        | K::RefExpression => true,
        K::Argument => {
            parent.child_token_of_kind(K::RefKeyword).is_some()
                || parent.child_token_of_kind(K::OutKeyword).is_some()
        }
        // `(a, b) = ...` writes both.
        K::TupleExpression => false,
        _ => false,
    }
}

/// Whether the name `node` is is only written, not read: the left of a
/// plain `=`, or passed `out`.
pub(crate) fn is_only_written(node: &SyntaxNode) -> bool {
    let Some(parent) = node.parent() else {
        return false;
    };
    match parent.kind() {
        SyntaxKind::SimpleAssignmentExpression => parent.children().next().as_ref() == Some(node),
        SyntaxKind::Argument => parent.child_token_of_kind(SyntaxKind::OutKeyword).is_some(),
        _ => false,
    }
}

/// Whether two pieces of syntax are the same code: the same tokens in the
/// same order, whatever the whitespace and comments between them.
pub(crate) fn same_tokens(a: &SyntaxNode, b: &SyntaxNode) -> bool {
    a.kind() == b.kind()
        && a.descendant_tokens()
            .map(|token| token.text().to_string())
            .eq(b.descendant_tokens().map(|token| token.text().to_string()))
}

/// The tokens of `node` joined by single spaces where the source had any
/// whitespace: a short, one-line rendering for a title.
pub(crate) fn one_line(node: &SyntaxNode) -> String {
    let text = node.text();
    let mut out = String::with_capacity(text.len());
    let mut space = false;
    for c in text.chars() {
        if c.is_whitespace() {
            space = true;
            continue;
        }
        if space && !out.is_empty() {
            out.push(' ');
        }
        space = false;
        out.push(c);
    }
    out
}

// MARK: - the view

impl<'a> View<'a> {
    /// The compiled project the view is of: for questions about other
    /// files, such as where else a name is used.
    pub(crate) fn project(&self) -> &'a crate::semantic::Semantic {
        self.semantic
    }

    /// The root of the file as the editor has it.
    pub(crate) fn syntax_root(&self) -> &SyntaxNode {
        &self.root
    }

    /// How `ty` is written at `at`: `int` for `System.Int32`, `int?` for a
    /// `Nullable<int>`, and a type from a namespace that no `using` in scope
    /// brings in with its namespace in front. `None` for a type there is no
    /// way to write: an anonymous type, or one the binder could not work
    /// out.
    pub(crate) fn display_type(&self, ty: &Type, at: &SyntaxNode) -> Option<String> {
        let in_scope: HashSet<SymbolId> = self.namespaces_in_scope(at).into_iter().collect();
        self.display_type_with(ty, &in_scope)
    }

    fn display_type_with(&self, ty: &Type, in_scope: &HashSet<SymbolId>) -> Option<String> {
        let symbols = self.compilation().symbols();
        Some(match ty {
            Type::Error | Type::Null => return None,
            Type::Void => "void".to_string(),
            Type::Dynamic => "dynamic".to_string(),
            Type::TypeParameter(symbol) => symbols.get(*symbol).name.clone(),
            Type::Pointer(inner) => format!("{}*", self.display_type_with(inner, in_scope)?),
            Type::ByRef(_) => return None,
            Type::FunctionPointer(_) => ty.display(symbols),
            Type::Array { element, rank } => {
                let commas = ",".repeat(rank.saturating_sub(1));
                format!("{}[{commas}]", self.display_type_with(element, in_scope)?)
            }
            Type::Tuple(elements) => {
                let mut parts = Vec::new();
                for element in elements {
                    let ty = self.display_type_with(&element.ty, in_scope)?;
                    parts.push(match &element.name {
                        Some(name) if !name.starts_with("Item") => format!("{ty} {name}"),
                        _ => ty,
                    });
                }
                format!("({})", parts.join(", "))
            }
            Type::Named {
                symbol,
                type_arguments,
            } => {
                let found = symbols.get(*symbol);
                if found.as_named_type().is_some_and(|named| named.anonymous)
                    || found.name.is_empty()
                    || found.name.contains('<')
                {
                    return None;
                }
                let qualified = symbols.qualified_name(*symbol);
                if let Some(special) = SpecialType::ALL
                    .iter()
                    .find(|special| special.metadata_name() == qualified)
                {
                    return Some(special.keyword().to_string());
                }
                if qualified == "System.Nullable`1" && type_arguments.len() == 1 {
                    return Some(format!(
                        "{}?",
                        self.display_type_with(&type_arguments[0], in_scope)?
                    ));
                }
                let mut parts = vec![found.name.clone()];
                let mut current = found.container;
                let mut namespace = None;
                while let Some(container) = current {
                    let parent = symbols.get(container);
                    if parent.kind == SymbolKind::NamedType {
                        parts.push(parent.name.clone());
                    } else {
                        namespace = Some(container);
                        break;
                    }
                    current = parent.container;
                }
                if let Some(namespace) = namespace
                    && namespace != self.compilation().global_namespace()
                    && !in_scope.contains(&namespace)
                {
                    parts.push(symbols.qualified_name(namespace));
                }
                parts.reverse();
                let mut name = parts.join(".");
                if !type_arguments.is_empty() {
                    let mut arguments = Vec::new();
                    for argument in type_arguments {
                        arguments.push(self.display_type_with(argument, in_scope)?);
                    }
                    name = format!("{name}<{}>", arguments.join(", "));
                }
                name
            }
        })
    }

    /// Every name a new declaration at `at` could collide with: the
    /// identifiers written anywhere in the member it is in, and the members
    /// of the types around it. Generous on purpose — a name that did not
    /// need to be avoided costs a `1` on the end, one that did costs a
    /// compile error.
    pub(crate) fn names_near(&self, at: &SyntaxNode) -> HashSet<String> {
        let scope = std::iter::once(at.clone())
            .chain(at.ancestors())
            .find(|ancestor| is_type_declaration(ancestor.kind()))
            .unwrap_or_else(|| self.root.clone());
        let mut names: HashSet<String> = scope
            .descendant_tokens()
            .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
            .map(|token| token.value_text().to_string())
            .collect();
        let context = self.model.binder().context_at(self.tree, at);
        let symbols = self.compilation().symbols();
        for ty in context.enclosing_types() {
            for &member in &symbols.get(ty).members {
                names.insert(symbols.get(member).name.clone());
            }
        }
        names
    }

    /// The type of the expression `node`, from the body it is in; `None`
    /// when the binder did not reach it or could not work it out.
    pub(crate) fn expression_type(&mut self, node: &SyntaxNode) -> Option<Type> {
        let body = self.body_for(node)?;
        match body.type_at(node.span())? {
            Type::Error => None,
            ty => Some(ty.clone()),
        }
    }

    /// The type a symbol holds: a field's, a property's, a parameter's.
    pub(crate) fn symbol_type(&self, symbol: SymbolId) -> Type {
        self.model.type_of_symbol(symbol)
    }

    /// The base class and interfaces of a type.
    pub(crate) fn base_types(&self, symbol: SymbolId) -> Vec<Type> {
        self.model.base_types_of(symbol)
    }

    /// The symbol `node` declares.
    pub(crate) fn declared(&self, node: &SyntaxNode) -> Option<SymbolId> {
        self.model.declared_symbol(node)
    }

    /// The compilation behind the view, for providers that look up types.
    pub(crate) fn compiled(&self) -> &rustlyn_semantics::Compilation {
        self.compilation()
    }

    /// The bound body `node` is in.
    pub(crate) fn bound_body(
        &mut self,
        node: &SyntaxNode,
    ) -> Option<std::sync::Arc<rustlyn_semantics::BoundBody>> {
        self.body_for(node)
    }
}

// MARK: - the context

impl Context<'_, '_> {
    /// The selection without the whitespace at its ends. A cursor stays an
    /// empty span.
    pub(crate) fn trimmed_span(&self) -> TextSpan {
        let text = slice(&self.text, self.span);
        let start = self.span.start() + (text.len() - text.trim_start().len()) as u32;
        let end = self.span.end() - (text.len() - text.trim_end().len()) as u32;
        TextSpan::from_bounds(start, end.max(start))
    }

    /// The token the cursor is on, or the one the selection starts with. A
    /// cursor right after a word is on the word.
    pub(crate) fn token_at_cursor(&self) -> Option<SyntaxToken> {
        let span = self.trimmed_span();
        let root = self.view.syntax_root();
        let at = root.find_token(span.start())?;
        if span.is_empty()
            && !at.span().contains(span.start())
            && let Some(before) = root.find_token(span.start().checked_sub(1)?)
            && before.span().end() == span.start()
        {
            return Some(before);
        }
        Some(at)
    }

    /// The node the selection covers exactly, when there is a selection.
    pub(crate) fn selected_node(&self) -> Option<SyntaxNode> {
        let span = self.trimmed_span();
        if span.is_empty() {
            return None;
        }
        node_exactly(self.view.syntax_root(), span)
    }

    /// The file's line ending.
    pub(crate) fn newline(&self) -> &'static str {
        newline(&self.text)
    }

    /// The file's indentation step.
    pub(crate) fn indent_unit(&self) -> String {
        indent_unit(&self.text)
    }

    /// The indentation of the line `offset` is on.
    pub(crate) fn indentation_at(&self, offset: u32) -> String {
        indentation_at(&self.text, offset)
    }

    /// The text of `span`.
    pub(crate) fn slice(&self, span: TextSpan) -> &str {
        slice(&self.text, span)
    }

    /// The innermost node of `kinds` around the cursor, the cursor's own
    /// token's parent included.
    pub(crate) fn ancestor_of_kind(&self, kinds: &[SyntaxKind]) -> Option<SyntaxNode> {
        let token = self.token_at_cursor()?;
        std::iter::once(token.parent().clone())
            .chain(token.parent().ancestors())
            .find(|node| kinds.contains(&node.kind()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_indentation_step_is_the_one_the_file_uses() {
        assert_eq!(
            indent_unit("class C\n{\n  void M()\n  {\n    x();\n  }\n}\n"),
            "  "
        );
        assert_eq!(indent_unit("class C\n{\n\tvoid M() { }\n}\n"), "\t");
        assert_eq!(indent_unit("class C { }\n"), "    ");
    }

    #[test]
    fn reindenting_moves_every_line_but_the_first() {
        let moved = reindent(
            "if (a)\n        {\n            b();\n        }",
            "        ",
            "    ",
        );
        assert_eq!(moved, "if (a)\n    {\n        b();\n    }");
    }

    #[test]
    fn a_fresh_name_counts_up_past_what_is_taken() {
        let taken: HashSet<String> = ["v".to_string(), "v1".to_string()].into();
        assert_eq!(fresh_name("v", &taken), "v2");
        assert_eq!(fresh_name("w", &taken), "w");
        assert_eq!(camel_case("_count"), "count");
        assert_eq!(camel_case("Class"), "@class");
        assert_eq!(pascal_case("_count"), "Count");
    }

    #[test]
    fn whole_lines_take_the_line_break_with_them() {
        let text = "a;\n    b;\nc;\n";
        let span = TextSpan::new(7, 2);
        assert_eq!(whole_lines(text, span), TextSpan::new(3, 7));
        let shared = "a; b;\n";
        assert_eq!(
            whole_lines(shared, TextSpan::new(3, 2)),
            TextSpan::new(3, 2)
        );
    }
}
