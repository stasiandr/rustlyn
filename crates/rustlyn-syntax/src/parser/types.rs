//! Names and types.
//!
//! Two places here need more than lookahead. `a < b` and `a<b>(c)` start the
//! same way, and `List<List<int>>` ends on a token the lexer has already
//! decided is a right shift; both are resolved the way Roslyn resolves them, by
//! trying and rewinding, and by splitting the shift token back apart.

use rustlyn_diagnostics::ErrorCode;
use rustlyn_text::TextSpan;

use super::facts::{can_start_expression, can_start_type, is_predefined_type};
use super::patterns::is_query_keyword;
use super::{Parser, node};
use crate::green::{GreenElement, green_token};
use crate::{SyntaxKind, Token, TokenValue, kind_from_text};

/// Where a type is being parsed, which decides what a trailing `?` means.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum TypeMode {
    /// A type is required here, so `?` always makes it nullable.
    Normal,
    /// A type inside a pattern or after `as`, where `?` may instead be the
    /// start of a conditional: `x is T ? a : b` is a conditional, but
    /// `x as int?` is a nullable type.
    Conditional,
}

impl Parser {
    // -- names -------------------------------------------------------------

    /// `identifier`, `identifier<...>`, `a.b.c` or `alias::name`.
    pub(crate) fn parse_name(&mut self, expression_context: bool) -> GreenElement {
        let mut left = if self.at(SyntaxKind::IdentifierToken)
            && self.nth_kind(1) == SyntaxKind::ColonColonToken
        {
            let alias = node(SyntaxKind::IdentifierName, vec![self.eat_token()]);
            let colons = self.eat_token();
            let right = self.parse_simple_name(expression_context);
            node(SyntaxKind::AliasQualifiedName, vec![alias, colons, right])
        } else {
            self.parse_simple_name(expression_context)
        };

        while self.at(SyntaxKind::DotToken) && self.nth_kind(1) == SyntaxKind::IdentifierToken {
            let ends_the_line = self.dot_ends_the_line();
            let dot = self.eat_token();
            let right = if ends_the_line {
                self.missing_name_after_dot()
            } else {
                self.parse_simple_name(expression_context)
            };
            left = node(SyntaxKind::QualifiedName, vec![left, dot, right]);
        }
        left
    }

    /// `identifier`, or `identifier<...>` when the angle brackets really are
    /// type arguments.
    pub(crate) fn parse_simple_name(&mut self, expression_context: bool) -> GreenElement {
        let name = self.expect_identifier();
        if self.at(SyntaxKind::LessThanToken)
            && self.scans_as_type_argument_list(expression_context)
        {
            let arguments = self.parse_type_argument_list();
            node(SyntaxKind::GenericName, vec![name, arguments])
        } else {
            node(SyntaxKind::IdentifierName, vec![name])
        }
    }

    /// Whether the `<` at the cursor opens a type argument list.
    ///
    /// In a type there is nothing else it could be. In an expression `a < b`
    /// is a comparison until proven otherwise, so the contents must parse as
    /// types *and* what follows the `>` must be something that can only come
    /// after a type argument list — Roslyn applies the same token set.
    fn scans_as_type_argument_list(&mut self, expression_context: bool) -> bool {
        self.speculate(|p| {
            if p.eat_if(SyntaxKind::LessThanToken).is_none() {
                return false;
            }
            loop {
                // `List<>` and `Dictionary<,>` name unbound generics.
                let omitted = p.at(SyntaxKind::CommaToken) || p.at_greater_than();
                if !omitted && !p.scan_type() {
                    return false;
                }
                if p.eat_if(SyntaxKind::CommaToken).is_some() {
                    continue;
                }
                break;
            }
            if !p.at_greater_than() {
                return false;
            }
            p.eat_greater_than();

            !expression_context
                || matches!(
                    p.kind(),
                    SyntaxKind::OpenParenToken
                        | SyntaxKind::CloseParenToken
                        | SyntaxKind::OpenBracketToken
                        | SyntaxKind::CloseBracketToken
                        | SyntaxKind::CloseBraceToken
                        | SyntaxKind::ColonToken
                        | SyntaxKind::SemicolonToken
                        | SyntaxKind::CommaToken
                        | SyntaxKind::DotToken
                        | SyntaxKind::QuestionToken
                        | SyntaxKind::EqualsEqualsToken
                        | SyntaxKind::ExclamationEqualsToken
                        | SyntaxKind::BarToken
                        | SyntaxKind::CaretToken
                        | SyntaxKind::AmpersandAmpersandToken
                        | SyntaxKind::BarBarToken
                        | SyntaxKind::AmpersandToken
                        | SyntaxKind::GreaterThanToken
                        | SyntaxKind::EndOfFileToken
                )
        })
    }

    fn parse_type_argument_list(&mut self) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::LessThanToken)];
        loop {
            if self.at(SyntaxKind::CommaToken) || self.at_greater_than() {
                children.push(node(SyntaxKind::OmittedTypeArgument, Vec::new()));
            } else {
                children.push(self.parse_type());
            }
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        children.push(self.eat_greater_than_or_missing());
        node(SyntaxKind::TypeArgumentList, children)
    }

    // -- the `>>` problem --------------------------------------------------

    /// Whether the current token starts with `>`.
    pub(crate) fn at_greater_than(&self) -> bool {
        self.kind().text().is_some_and(|text| text.starts_with('>'))
    }

    /// Consumes one `>`, splitting a wider token such as `>>` if needed.
    ///
    /// The lexer is right to read `>>` as a right shift — that is what it means
    /// almost everywhere — so closing `List<List<int>>` means taking the token
    /// back apart. The leftover `>` is put back in the stream with the original
    /// trailing trivia, which keeps the file reconstructible.
    fn eat_greater_than(&mut self) -> GreenElement {
        debug_assert!(self.at_greater_than());
        if self.at(SyntaxKind::GreaterThanToken) {
            return self.eat_token();
        }

        let token = self.tokens[self.index].clone();
        let split = token.span.start() + 1;
        let leading_trivia = token.leading_trivia.clone();
        let trailing_trivia = token.trailing_trivia.clone();
        let rest_span = TextSpan::from_bounds(split, token.span.end());
        let rest_kind = kind_from_text(self.source.slice(rest_span))
            .expect("the tail of a `>`-token is itself a token");

        let first = Token {
            kind: SyntaxKind::GreaterThanToken,
            contextual_kind: SyntaxKind::GreaterThanToken,
            span: TextSpan::from_bounds(token.span.start(), split),
            full_span: TextSpan::from_bounds(token.full_span.start(), split),
            leading_trivia,
            trailing_trivia: Vec::new(),
            value: TokenValue::None,
            value_text: None,
        };
        self.splits.push((self.index, token.clone()));
        self.tokens[self.index] = Token {
            kind: rest_kind,
            contextual_kind: rest_kind,
            span: rest_span,
            full_span: TextSpan::from_bounds(split, token.full_span.end()),
            leading_trivia: Vec::new(),
            trailing_trivia,
            value: TokenValue::None,
            value_text: None,
        };

        GreenElement::Token(green_token(&first, &self.source, &mut self.cache))
    }

    fn eat_greater_than_or_missing(&mut self) -> GreenElement {
        if self.at_greater_than() {
            self.eat_greater_than()
        } else {
            self.expect(SyntaxKind::GreaterThanToken)
        }
    }

    // -- types -------------------------------------------------------------

    pub(crate) fn parse_type(&mut self) -> GreenElement {
        self.parse_type_in(TypeMode::Normal)
    }

    pub(crate) fn parse_type_in(&mut self, mode: TypeMode) -> GreenElement {
        if self.at(SyntaxKind::RefKeyword) {
            let mut children = vec![self.eat_token()];
            if let Some(readonly) = self.eat_if(SyntaxKind::ReadOnlyKeyword) {
                children.push(readonly);
            }
            children.push(self.parse_type_in(mode));
            return node(SyntaxKind::RefType, children);
        }

        if self.at_contextual(SyntaxKind::ScopedKeyword) && can_start_type(self.nth_kind(1)) {
            let scoped = self.eat_token_as(SyntaxKind::ScopedKeyword);
            let inner = self.parse_type_in(mode);
            return node(SyntaxKind::ScopedType, vec![scoped, inner]);
        }

        let mut ty = self.parse_type_core();

        loop {
            match self.kind() {
                SyntaxKind::QuestionToken if self.question_makes_nullable(mode) => {
                    let question = self.eat_token();
                    ty = node(SyntaxKind::NullableType, vec![ty, question]);
                }
                SyntaxKind::AsteriskToken => {
                    let star = self.eat_token();
                    ty = node(SyntaxKind::PointerType, vec![ty, star]);
                }
                SyntaxKind::OpenBracketToken if self.at_rank_specifier() => {
                    let mut children = vec![ty];
                    while self.at_rank_specifier() {
                        children.push(self.parse_array_rank_specifier(false));
                    }
                    ty = node(SyntaxKind::ArrayType, children);
                }
                _ => break,
            }
        }
        ty
    }

    /// Whether a `?` here makes the type nullable rather than opening a
    /// conditional expression.
    fn question_makes_nullable(&self, mode: TypeMode) -> bool {
        match mode {
            TypeMode::Normal => true,
            // `x as int?;` is a nullable type, `x is T ? a : b` is not: the
            // difference is whether an expression can follow the `?`.
            TypeMode::Conditional => {
                !can_start_expression(self.nth_kind(1))
                    // `x is object?[] a` is an array of nullable: a `?`
                    // straight before an empty rank is never a conditional,
                    // whose branch would be a collection expression.
                    || (self.nth_kind(1) == SyntaxKind::OpenBracketToken
                        && matches!(
                            self.nth_kind(2),
                            SyntaxKind::CloseBracketToken | SyntaxKind::CommaToken
                        ))
                    // Inside a query the query keywords are reserved, so the
                    // `select` of `as T? select x` cannot be an expression.
                    || (self.in_query() && is_query_keyword(self.nth_contextual_kind(1)))
            }
        }
    }

    fn parse_type_core(&mut self) -> GreenElement {
        if self.at(SyntaxKind::DelegateKeyword) && self.nth_kind(1) == SyntaxKind::AsteriskToken {
            return self.parse_function_pointer_type();
        }
        if is_predefined_type(self.kind()) {
            return node(SyntaxKind::PredefinedType, vec![self.eat_token()]);
        }
        if self.at(SyntaxKind::OpenParenToken) {
            return self.parse_tuple_type();
        }
        if self.at(SyntaxKind::IdentifierToken) {
            return self.parse_name(false);
        }

        let text = self.current_text();
        self.error_at_current(ErrorCode::ErrTypeExpected, &[&text]);
        node(
            SyntaxKind::IdentifierName,
            vec![Self::missing(SyntaxKind::IdentifierToken)],
        )
    }

    /// `delegate*<int, void>`, `delegate* managed<int, int>` and
    /// `delegate* unmanaged[Cdecl, SuppressGCTransition]<int, void>`.
    ///
    /// The last type argument is the return type, which is why the parameters
    /// are a list of their own rather than a type argument list: `void` may
    /// stand there but nowhere else.
    pub(crate) fn parse_function_pointer_type(&mut self) -> GreenElement {
        let mut children = vec![self.eat_token(), self.expect(SyntaxKind::AsteriskToken)];

        if self.at_contextual(SyntaxKind::ManagedKeyword)
            || self.at_contextual(SyntaxKind::UnmanagedKeyword)
        {
            let unmanaged = self.at_contextual(SyntaxKind::UnmanagedKeyword);
            let keyword = self.eat_token_as(if unmanaged {
                SyntaxKind::UnmanagedKeyword
            } else {
                SyntaxKind::ManagedKeyword
            });
            let mut convention = vec![keyword];
            // Only `unmanaged` takes a list, and `[` after `managed` would be
            // an array of function pointers instead.
            if unmanaged && self.at(SyntaxKind::OpenBracketToken) {
                convention.push(self.parse_unmanaged_calling_convention_list());
            }
            children.push(node(
                SyntaxKind::FunctionPointerCallingConvention,
                convention,
            ));
        }

        let mut parameters = vec![self.expect(SyntaxKind::LessThanToken)];
        loop {
            let mut parameter = Vec::new();
            while matches!(
                self.kind(),
                SyntaxKind::RefKeyword
                    | SyntaxKind::OutKeyword
                    | SyntaxKind::InKeyword
                    | SyntaxKind::ReadOnlyKeyword
            ) {
                parameter.push(self.eat_token());
            }
            parameter.push(self.parse_type());
            parameters.push(node(SyntaxKind::FunctionPointerParameter, parameter));
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => parameters.push(comma),
                None => break,
            }
        }
        parameters.push(self.eat_greater_than_or_missing());

        children.push(node(SyntaxKind::FunctionPointerParameterList, parameters));
        node(SyntaxKind::FunctionPointerType, children)
    }

    fn parse_unmanaged_calling_convention_list(&mut self) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::OpenBracketToken)];
        loop {
            children.push(node(
                SyntaxKind::FunctionPointerUnmanagedCallingConvention,
                vec![self.expect_identifier()],
            ));
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        children.push(self.expect(SyntaxKind::CloseBracketToken));
        node(
            SyntaxKind::FunctionPointerUnmanagedCallingConventionList,
            children,
        )
    }

    pub(crate) fn parse_tuple_type(&mut self) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::OpenParenToken)];
        loop {
            let ty = self.parse_type();
            let element = if self.at(SyntaxKind::IdentifierToken) {
                let name = self.eat_token();
                node(SyntaxKind::TupleElement, vec![ty, name])
            } else {
                node(SyntaxKind::TupleElement, vec![ty])
            };
            children.push(element);
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        children.push(self.expect(SyntaxKind::CloseParenToken));
        node(SyntaxKind::TupleType, children)
    }

    /// Whether `[` here opens an array rank specifier such as `[]` or `[,]`
    /// rather than an indexer or an attribute.
    fn at_rank_specifier(&self) -> bool {
        self.at(SyntaxKind::OpenBracketToken)
            && matches!(
                self.nth_kind(1),
                SyntaxKind::CloseBracketToken | SyntaxKind::CommaToken
            )
    }

    /// `[]`, `[,]` or, when `allow_sizes`, `[3, 4]`.
    pub(crate) fn parse_array_rank_specifier(&mut self, allow_sizes: bool) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::OpenBracketToken)];
        loop {
            if self.at(SyntaxKind::CloseBracketToken) || self.at(SyntaxKind::CommaToken) {
                children.push(node(SyntaxKind::OmittedArraySizeExpression, Vec::new()));
            } else if allow_sizes {
                children.push(self.parse_expression());
            } else {
                children.push(node(SyntaxKind::OmittedArraySizeExpression, Vec::new()));
            }
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        children.push(self.expect(SyntaxKind::CloseBracketToken));
        node(SyntaxKind::ArrayRankSpecifier, children)
    }

    // -- speculation helpers ----------------------------------------------

    /// Parses a type, reporting whether it came out clean.
    ///
    /// Reusing the real parser instead of a separate scanner keeps one
    /// description of the grammar. Roslyn keeps a second, faster one; the cost
    /// here is speed on backtracking, which has not mattered yet.
    pub(crate) fn scan_type(&mut self) -> bool {
        self.scan_type_in(TypeMode::Normal)
    }

    /// Parses a type in the given mode, reporting whether it came out clean.
    pub(crate) fn scan_type_in(&mut self, mode: TypeMode) -> bool {
        let before = self.diagnostics.len();
        self.parse_type_in(mode);
        self.diagnostics.len() == before
    }
}
