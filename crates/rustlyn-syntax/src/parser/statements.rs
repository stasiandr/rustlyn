//! Statements.
//!
//! The hard part is not the control-flow keywords, which announce themselves,
//! but telling a declaration from an expression. `a.b c;` declares a variable
//! and `a.b(c);` calls a method, and nothing short of parsing the type and
//! looking at what follows can tell them apart — so that is what happens here,
//! behind a reset point.

use rustlyn_diagnostics::ErrorCode;

use super::facts::is_predefined_type;
use super::{Parser, node};
use crate::SyntaxKind;
use crate::green::GreenElement;

impl Parser {
    /// `{ ... }`
    pub(crate) fn parse_block(&mut self) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::OpenBraceToken)];
        while !self.at(SyntaxKind::CloseBraceToken) && !self.at_end() {
            let before = self.index;
            children.push(self.parse_statement());
            if self.index == before {
                // The statement parser could not get anywhere; drop tokens
                // until something recognisable turns up so the loop ends.
                match self.skip_tokens(ErrorCode::ErrInvalidExprTerm, |p| {
                    p.at(SyntaxKind::CloseBraceToken) || p.at(SyntaxKind::SemicolonToken)
                }) {
                    Some(skipped) => children.push(skipped),
                    None => break,
                }
            }
        }
        children.push(self.expect(SyntaxKind::CloseBraceToken));
        node(SyntaxKind::Block, children)
    }

    pub(crate) fn parse_statement(&mut self) -> GreenElement {
        match self.kind() {
            SyntaxKind::OpenBraceToken => self.parse_block(),
            SyntaxKind::SemicolonToken => node(SyntaxKind::EmptyStatement, vec![self.eat_token()]),
            SyntaxKind::IfKeyword => self.parse_if_statement(),
            SyntaxKind::WhileKeyword => self.parse_while_statement(),
            SyntaxKind::DoKeyword => self.parse_do_statement(),
            SyntaxKind::ForKeyword => self.parse_for_statement(),
            SyntaxKind::ForEachKeyword => self.parse_foreach_statement(),
            SyntaxKind::SwitchKeyword => self.parse_switch_statement(),
            SyntaxKind::TryKeyword => self.parse_try_statement(),
            SyntaxKind::UsingKeyword if self.nth_kind(1) == SyntaxKind::OpenParenToken => {
                self.parse_using_statement()
            }
            SyntaxKind::LockKeyword => self.parse_lock_statement(),
            SyntaxKind::FixedKeyword => self.parse_fixed_statement(),
            SyntaxKind::CheckedKeyword => self.parse_keyword_block(SyntaxKind::CheckedStatement),
            SyntaxKind::UncheckedKeyword => {
                self.parse_keyword_block(SyntaxKind::UncheckedStatement)
            }
            SyntaxKind::UnsafeKeyword if self.nth_kind(1) == SyntaxKind::OpenBraceToken => {
                self.parse_keyword_block(SyntaxKind::UnsafeStatement)
            }
            SyntaxKind::BreakKeyword => self.parse_jump(SyntaxKind::BreakStatement, false),
            SyntaxKind::ContinueKeyword => self.parse_jump(SyntaxKind::ContinueStatement, false),
            SyntaxKind::ReturnKeyword => self.parse_jump(SyntaxKind::ReturnStatement, true),
            SyntaxKind::ThrowKeyword => self.parse_jump(SyntaxKind::ThrowStatement, true),
            SyntaxKind::GotoKeyword => self.parse_goto_statement(),
            SyntaxKind::OpenBracketToken if self.at_local_function() => self.parse_local_function(),
            _ if self.at_await_statement() => self.parse_await_statement(),
            _ if self.at_yield_statement() => self.parse_yield_statement(),
            _ if self.at_labeled_statement() => self.parse_labeled_statement(),
            _ if self.at_local_function() => self.parse_local_function(),
            _ if self.at_local_declaration() => self.parse_local_declaration(),
            _ => {
                let expression = self.parse_expression();
                let semicolon = self.expect(SyntaxKind::SemicolonToken);
                node(SyntaxKind::ExpressionStatement, vec![expression, semicolon])
            }
        }
    }

    /// A statement in a position that takes exactly one, as after `if (...)`.
    fn parse_embedded_statement(&mut self) -> GreenElement {
        self.parse_statement()
    }

    // -- control flow ------------------------------------------------------

    fn parse_if_statement(&mut self) -> GreenElement {
        let keyword = self.expect(SyntaxKind::IfKeyword);
        let open = self.expect(SyntaxKind::OpenParenToken);
        let condition = self.parse_expression();
        let close = self.expect(SyntaxKind::CloseParenToken);
        let then = self.parse_embedded_statement();

        let mut children = vec![keyword, open, condition, close, then];
        if self.at(SyntaxKind::ElseKeyword) {
            let else_keyword = self.eat_token();
            let otherwise = self.parse_embedded_statement();
            children.push(node(SyntaxKind::ElseClause, vec![else_keyword, otherwise]));
        }
        node(SyntaxKind::IfStatement, children)
    }

    fn parse_while_statement(&mut self) -> GreenElement {
        let keyword = self.expect(SyntaxKind::WhileKeyword);
        let open = self.expect(SyntaxKind::OpenParenToken);
        let condition = self.parse_expression();
        let close = self.expect(SyntaxKind::CloseParenToken);
        let body = self.parse_embedded_statement();
        node(
            SyntaxKind::WhileStatement,
            vec![keyword, open, condition, close, body],
        )
    }

    fn parse_do_statement(&mut self) -> GreenElement {
        let keyword = self.expect(SyntaxKind::DoKeyword);
        let body = self.parse_embedded_statement();
        let while_keyword = self.expect(SyntaxKind::WhileKeyword);
        let open = self.expect(SyntaxKind::OpenParenToken);
        let condition = self.parse_expression();
        let close = self.expect(SyntaxKind::CloseParenToken);
        let semicolon = self.expect(SyntaxKind::SemicolonToken);
        node(
            SyntaxKind::DoStatement,
            vec![
                keyword,
                body,
                while_keyword,
                open,
                condition,
                close,
                semicolon,
            ],
        )
    }

    fn parse_for_statement(&mut self) -> GreenElement {
        let mut children = vec![
            self.expect(SyntaxKind::ForKeyword),
            self.expect(SyntaxKind::OpenParenToken),
        ];

        if !self.at(SyntaxKind::SemicolonToken) {
            if self.at_local_declaration() {
                children.push(self.parse_variable_declaration());
            } else {
                children.push(self.parse_expression());
                while let Some(comma) = self.eat_if(SyntaxKind::CommaToken) {
                    children.push(comma);
                    children.push(self.parse_expression());
                }
            }
        }
        children.push(self.expect(SyntaxKind::SemicolonToken));

        if !self.at(SyntaxKind::SemicolonToken) {
            children.push(self.parse_expression());
        }
        children.push(self.expect(SyntaxKind::SemicolonToken));

        if !self.at(SyntaxKind::CloseParenToken) {
            children.push(self.parse_expression());
            while let Some(comma) = self.eat_if(SyntaxKind::CommaToken) {
                children.push(comma);
                children.push(self.parse_expression());
            }
        }
        children.push(self.expect(SyntaxKind::CloseParenToken));
        children.push(self.parse_embedded_statement());
        node(SyntaxKind::ForStatement, children)
    }

    fn parse_foreach_statement(&mut self) -> GreenElement {
        let mut children = vec![
            self.expect(SyntaxKind::ForEachKeyword),
            self.expect(SyntaxKind::OpenParenToken),
        ];

        // `foreach (var (a, b) in pairs)` deconstructs instead of declaring one
        // variable, and gets its own node kind. `foreach ((int a, int b) pair
        // in pairs)` looks the same up to the `)`, and is a tuple-typed
        // variable with a name; only what follows the group tells them apart.
        let deconstructing = (self.at_contextual(SyntaxKind::VarKeyword)
            && self.nth_kind(1) == SyntaxKind::OpenParenToken)
            || (self.at(SyntaxKind::OpenParenToken) && self.at_deconstruction_target());

        if deconstructing {
            // The variable may be `var (a, b)` or a tuple of declarations such
            // as `(int a, string b)`; both are expressions here.
            children.push(self.parse_expression());
        } else {
            children.push(self.parse_type());
            children.push(self.expect_identifier());
        }

        children.push(self.expect(SyntaxKind::InKeyword));
        children.push(self.parse_expression());
        children.push(self.expect(SyntaxKind::CloseParenToken));
        children.push(self.parse_embedded_statement());

        node(
            if deconstructing {
                SyntaxKind::ForEachVariableStatement
            } else {
                SyntaxKind::ForEachStatement
            },
            children,
        )
    }

    fn parse_switch_statement(&mut self) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::SwitchKeyword)];

        // `switch (a, b)` switches on a tuple: the parentheses belong to the
        // expression, and the statement has none of its own.
        let governs_a_tuple = self.switch_governs_a_tuple();
        if !governs_a_tuple {
            children.push(self.expect(SyntaxKind::OpenParenToken));
        }
        children.push(self.parse_expression());
        if !governs_a_tuple {
            children.push(self.expect(SyntaxKind::CloseParenToken));
        }
        children.push(self.expect(SyntaxKind::OpenBraceToken));

        while !self.at(SyntaxKind::CloseBraceToken) && !self.at_end() {
            let before = self.index;
            children.push(self.parse_switch_section());
            if self.index == before {
                break;
            }
        }

        children.push(self.expect(SyntaxKind::CloseBraceToken));
        node(SyntaxKind::SwitchStatement, children)
    }

    /// Whether the parentheses after `switch` hold a tuple rather than the
    /// statement's own parentheses, which shows up as a comma between them.
    fn switch_governs_a_tuple(&mut self) -> bool {
        self.speculate(|p| {
            if p.eat_if(SyntaxKind::OpenParenToken).is_none() {
                return false;
            }
            let mut depth = 1usize;
            loop {
                match p.kind() {
                    SyntaxKind::OpenParenToken | SyntaxKind::OpenBracketToken => {
                        depth += 1;
                        p.eat_token();
                    }
                    SyntaxKind::CloseParenToken | SyntaxKind::CloseBracketToken => {
                        depth -= 1;
                        p.eat_token();
                        if depth == 0 {
                            return false;
                        }
                    }
                    SyntaxKind::CommaToken if depth == 1 => return true,
                    SyntaxKind::EndOfFileToken | SyntaxKind::OpenBraceToken => return false,
                    _ => {
                        p.eat_token();
                    }
                }
            }
        })
    }

    fn parse_switch_section(&mut self) -> GreenElement {
        let mut children = Vec::new();
        while self.at(SyntaxKind::CaseKeyword) || self.at(SyntaxKind::DefaultKeyword) {
            children.push(self.parse_switch_label());
        }
        while !self.at(SyntaxKind::CaseKeyword)
            && !self.at(SyntaxKind::DefaultKeyword)
            && !self.at(SyntaxKind::CloseBraceToken)
            && !self.at_end()
        {
            let before = self.index;
            children.push(self.parse_statement());
            if self.index == before {
                break;
            }
        }
        node(SyntaxKind::SwitchSection, children)
    }

    fn parse_switch_label(&mut self) -> GreenElement {
        if self.at(SyntaxKind::DefaultKeyword) {
            let keyword = self.eat_token();
            let colon = self.expect(SyntaxKind::ColonToken);
            return node(SyntaxKind::DefaultSwitchLabel, vec![keyword, colon]);
        }

        let keyword = self.expect(SyntaxKind::CaseKeyword);

        // `case A | B:` is a constant built with an operator a pattern would
        // never allow, so try the whole thing as an expression first and keep
        // it only if a `:` follows. Not when a type is followed by a name,
        // though: `case ImmutableHashSet<T> a:` reads as `(X < T) > a` and
        // reaches the colon just fine, and is a declaration all the same —
        // no expression is a type followed by an identifier.
        // `case []:` and `case [var x]:` are list patterns: a `[` after
        // `case` never starts a constant, however well `[]` reads as a
        // collection expression.
        if !self.at(SyntaxKind::OpenBracketToken)
            && !self.case_label_declares_a_variable()
            && !self.case_label_deconstructs()
            && self.case_label_is_an_expression()
        {
            let value = self.parse_expression();
            let colon = self.expect(SyntaxKind::ColonToken);
            return node(SyntaxKind::CaseSwitchLabel, vec![keyword, value, colon]);
        }

        let pattern = self.parse_pattern();

        // A constant is the classic `case 1:`; anything else is a pattern
        // label, which may carry a `when` clause.
        if pattern.kind() == SyntaxKind::ConstantPattern
            && !self.at_contextual(SyntaxKind::WhenKeyword)
        {
            let value = pattern
                .as_node()
                .expect("a constant pattern is a node")
                .children()[0]
                .clone();
            let colon = self.expect(SyntaxKind::ColonToken);
            return node(SyntaxKind::CaseSwitchLabel, vec![keyword, value, colon]);
        }

        let mut children = vec![keyword, pattern];
        if let Some(clause) = self.parse_when_clause() {
            children.push(clause);
        }
        children.push(self.expect(SyntaxKind::ColonToken));
        node(SyntaxKind::CasePatternSwitchLabel, children)
    }

    /// Whether what follows `case` is a type and then `(`: `case C():` takes
    /// a `C` apart, since no call is a constant — `nameof(x)` aside.
    fn case_label_deconstructs(&mut self) -> bool {
        !self.at_contextual(SyntaxKind::NameOfKeyword)
            && self.speculate(|p| {
                p.at(SyntaxKind::IdentifierToken)
                    && p.scan_type()
                    && p.at(SyntaxKind::OpenParenToken)
            })
    }

    /// Whether what follows `case` is a type and then a name: `case T x:`.
    fn case_label_declares_a_variable(&mut self) -> bool {
        self.speculate(|p| {
            (p.at(SyntaxKind::IdentifierToken) || is_predefined_type(p.kind()))
                && p.scan_type()
                && p.at_identifier_designation()
        })
    }

    /// Whether what follows `case` parses as an expression ending at the `:`.
    fn case_label_is_an_expression(&mut self) -> bool {
        self.speculate(|p| {
            let before = p.diagnostics.len();
            let value = p.parse_expression();
            // `case (Kind.A, _):` parses as a tuple and ends at the colon,
            // and is still not a constant: no tuple is one. A parenthesised
            // list after `case` is a positional pattern, whatever it would
            // read as.
            if value.kind() == SyntaxKind::TupleExpression {
                return false;
            }
            // `case int[]:` and `case (int[]):` read as indexing with
            // nothing, which no expression is: it is the array type, tested
            // for.
            if indexes_with_nothing(&value) {
                return false;
            }
            p.diagnostics.len() == before && p.at(SyntaxKind::ColonToken)
        })
    }

    fn parse_try_statement(&mut self) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::TryKeyword), self.parse_block()];

        while self.at(SyntaxKind::CatchKeyword) {
            let keyword = self.eat_token();
            let mut clause = vec![keyword];
            if self.at(SyntaxKind::OpenParenToken) {
                let open = self.eat_token();
                let ty = self.parse_type();
                let mut declaration = vec![open, ty];
                if self.at(SyntaxKind::IdentifierToken) {
                    declaration.push(self.eat_token());
                }
                declaration.push(self.expect(SyntaxKind::CloseParenToken));
                clause.push(node(SyntaxKind::CatchDeclaration, declaration));
            }
            if let Some(when) = self.eat_contextual(SyntaxKind::WhenKeyword) {
                let open = self.expect(SyntaxKind::OpenParenToken);
                let condition = self.parse_expression();
                let close = self.expect(SyntaxKind::CloseParenToken);
                clause.push(node(
                    SyntaxKind::CatchFilterClause,
                    vec![when, open, condition, close],
                ));
            }
            clause.push(self.parse_block());
            children.push(node(SyntaxKind::CatchClause, clause));
        }

        if self.at(SyntaxKind::FinallyKeyword) {
            let keyword = self.eat_token();
            let block = self.parse_block();
            children.push(node(SyntaxKind::FinallyClause, vec![keyword, block]));
        }

        node(SyntaxKind::TryStatement, children)
    }

    fn parse_using_statement(&mut self) -> GreenElement {
        let keyword = self.expect(SyntaxKind::UsingKeyword);
        let open = self.expect(SyntaxKind::OpenParenToken);
        let resource = if self.at_local_declaration() {
            self.parse_variable_declaration()
        } else {
            self.parse_expression()
        };
        let close = self.expect(SyntaxKind::CloseParenToken);
        let body = self.parse_embedded_statement();
        node(
            SyntaxKind::UsingStatement,
            vec![keyword, open, resource, close, body],
        )
    }

    fn parse_lock_statement(&mut self) -> GreenElement {
        let keyword = self.expect(SyntaxKind::LockKeyword);
        let open = self.expect(SyntaxKind::OpenParenToken);
        let expression = self.parse_expression();
        let close = self.expect(SyntaxKind::CloseParenToken);
        let body = self.parse_embedded_statement();
        node(
            SyntaxKind::LockStatement,
            vec![keyword, open, expression, close, body],
        )
    }

    fn parse_fixed_statement(&mut self) -> GreenElement {
        let keyword = self.expect(SyntaxKind::FixedKeyword);
        let open = self.expect(SyntaxKind::OpenParenToken);
        let declaration = self.parse_variable_declaration();
        let close = self.expect(SyntaxKind::CloseParenToken);
        let body = self.parse_embedded_statement();
        node(
            SyntaxKind::FixedStatement,
            vec![keyword, open, declaration, close, body],
        )
    }

    fn parse_keyword_block(&mut self, kind: SyntaxKind) -> GreenElement {
        let keyword = self.eat_token();
        let block = self.parse_block();
        node(kind, vec![keyword, block])
    }

    /// `break;`, `continue;`, `return expr?;`, `throw expr?;`
    fn parse_jump(&mut self, kind: SyntaxKind, takes_value: bool) -> GreenElement {
        let keyword = self.eat_token();
        let mut children = vec![keyword];
        if takes_value && !self.at(SyntaxKind::SemicolonToken) {
            children.push(self.parse_expression());
        }
        // `break outer;` and `continue outer;` name the labeled loop they
        // leave (C# 15); the label is a name like `goto`'s, not an expression.
        if matches!(
            kind,
            SyntaxKind::BreakStatement | SyntaxKind::ContinueStatement
        ) && self.at(SyntaxKind::IdentifierToken)
        {
            children.push(self.eat_token());
        }
        children.push(self.expect(SyntaxKind::SemicolonToken));
        node(kind, children)
    }

    fn parse_goto_statement(&mut self) -> GreenElement {
        let keyword = self.expect(SyntaxKind::GotoKeyword);
        let (kind, mut children) = match self.kind() {
            SyntaxKind::CaseKeyword => {
                let case = self.eat_token();
                let value = self.parse_expression();
                (SyntaxKind::GotoCaseStatement, vec![keyword, case, value])
            }
            SyntaxKind::DefaultKeyword => {
                let default = self.eat_token();
                (SyntaxKind::GotoDefaultStatement, vec![keyword, default])
            }
            _ => {
                let label = self.expect_identifier();
                (SyntaxKind::GotoStatement, vec![keyword, label])
            }
        };
        children.push(self.expect(SyntaxKind::SemicolonToken));
        node(kind, children)
    }

    // -- contextual statements --------------------------------------------

    fn at_yield_statement(&self) -> bool {
        self.at_contextual(SyntaxKind::YieldKeyword)
            && matches!(
                self.nth_kind(1),
                SyntaxKind::ReturnKeyword | SyntaxKind::BreakKeyword
            )
    }

    fn parse_yield_statement(&mut self) -> GreenElement {
        let keyword = self.eat_token_as(SyntaxKind::YieldKeyword);
        if self.at(SyntaxKind::BreakKeyword) {
            let break_keyword = self.eat_token();
            let semicolon = self.expect(SyntaxKind::SemicolonToken);
            return node(
                SyntaxKind::YieldBreakStatement,
                vec![keyword, break_keyword, semicolon],
            );
        }
        let return_keyword = self.expect(SyntaxKind::ReturnKeyword);
        let value = self.parse_expression();
        let semicolon = self.expect(SyntaxKind::SemicolonToken);
        node(
            SyntaxKind::YieldReturnStatement,
            vec![keyword, return_keyword, value, semicolon],
        )
    }

    /// `await using (...)` and `await foreach (...)`, where the `await` belongs
    /// to the statement rather than to an expression.
    fn at_await_statement(&self) -> bool {
        self.at_contextual(SyntaxKind::AwaitKeyword)
            && matches!(
                self.nth_kind(1),
                SyntaxKind::UsingKeyword | SyntaxKind::ForEachKeyword
            )
    }

    fn parse_await_statement(&mut self) -> GreenElement {
        let keyword = self.eat_token_as(SyntaxKind::AwaitKeyword);
        let inner = if self.nth_kind(1) == SyntaxKind::OpenParenToken
            && self.at(SyntaxKind::UsingKeyword)
        {
            self.parse_using_statement()
        } else if self.at(SyntaxKind::ForEachKeyword) {
            self.parse_foreach_statement()
        } else {
            self.parse_local_declaration()
        };
        prepend(keyword, inner)
    }

    fn at_labeled_statement(&self) -> bool {
        self.at(SyntaxKind::IdentifierToken) && self.nth_kind(1) == SyntaxKind::ColonToken
    }

    fn parse_labeled_statement(&mut self) -> GreenElement {
        let label = self.eat_token();
        let colon = self.eat_token();
        let statement = self.parse_statement();
        node(SyntaxKind::LabeledStatement, vec![label, colon, statement])
    }

    // -- declarations ------------------------------------------------------

    /// Whether a local function declaration starts here.
    fn at_local_function(&mut self) -> bool {
        self.speculate(|p| {
            // A local function may carry attributes, as `[Conditional("DEBUG")]
            // static void Log()` does.
            let decorated = p.at(SyntaxKind::OpenBracketToken);
            while p.at(SyntaxKind::OpenBracketToken) {
                p.parse_attribute_lists();
            }
            // Only a declaration that says where its body lives may end at a
            // semicolon instead of having one.
            let mut imported = decorated;
            while p.at(SyntaxKind::StaticKeyword)
                || p.at(SyntaxKind::UnsafeKeyword)
                || p.at(SyntaxKind::ExternKeyword)
                || p.at_async_modifier()
            {
                imported |= p.at(SyntaxKind::ExternKeyword);
                p.eat_token();
            }
            if !p.scan_type() {
                return false;
            }
            if !p.at(SyntaxKind::IdentifierToken) {
                return false;
            }
            p.eat_token();

            // Step over any type parameters, accepting only what one can
            // contain, so that `= f(x)` is not mistaken for `<T>(x)`.
            if p.at(SyntaxKind::LessThanToken) {
                let mut angle = 0i32;
                loop {
                    match p.kind() {
                        SyntaxKind::LessThanToken => {
                            angle += 1;
                            p.eat_token();
                        }
                        SyntaxKind::GreaterThanToken => {
                            angle -= 1;
                            p.eat_token();
                            if angle <= 0 {
                                break;
                            }
                        }
                        SyntaxKind::IdentifierToken
                        | SyntaxKind::CommaToken
                        | SyntaxKind::InKeyword
                        | SyntaxKind::OutKeyword => {
                            p.eat_token();
                        }
                        _ => return false,
                    }
                }
            }
            if !p.at(SyntaxKind::OpenParenToken) {
                return false;
            }
            let mut depth = 0usize;
            loop {
                match p.kind() {
                    SyntaxKind::OpenParenToken => {
                        depth += 1;
                        p.eat_token();
                    }
                    SyntaxKind::CloseParenToken => {
                        depth -= 1;
                        p.eat_token();
                        if depth == 0 {
                            break;
                        }
                    }
                    SyntaxKind::EndOfFileToken => return false,
                    _ => {
                        p.eat_token();
                    }
                }
            }

            // A body has to follow. Without this, `await Setup(x);` in a
            // method that is not async reads as a local function named `Setup`
            // returning a type called `await`.
            //
            // The exception is a declaration that says where its body lives:
            // `[DllImport(...)] static extern bool F(...);` ends at a
            // semicolon, and nothing without an attribute or `extern` does.
            matches!(
                p.kind(),
                SyntaxKind::OpenBraceToken | SyntaxKind::EqualsGreaterThanToken
            ) || p.at_contextual(SyntaxKind::WhereKeyword)
                || (imported && p.at(SyntaxKind::SemicolonToken))
        })
    }

    /// Whether an `async` here modifies a local function rather than being
    /// its return type: `async f() => new async();` returns an `async`, since
    /// a modifier would leave `f` a type with no name after it.
    fn at_async_modifier(&mut self) -> bool {
        self.at_contextual(SyntaxKind::AsyncKeyword)
            && !(self.nth_kind(1) == SyntaxKind::IdentifierToken
                && self.nth_kind(2) == SyntaxKind::OpenParenToken)
    }

    fn parse_local_function(&mut self) -> GreenElement {
        let mut children = self.parse_attribute_lists();
        while self.at(SyntaxKind::StaticKeyword)
            || self.at(SyntaxKind::UnsafeKeyword)
            || self.at(SyntaxKind::ExternKeyword)
            || self.at_async_modifier()
        {
            children.push(if self.at_contextual(SyntaxKind::AsyncKeyword) {
                self.eat_token_as(SyntaxKind::AsyncKeyword)
            } else {
                self.eat_token()
            });
        }
        children.push(self.parse_type());
        children.push(self.expect_identifier());
        if self.at(SyntaxKind::LessThanToken) {
            children.push(self.parse_type_parameter_list());
        }
        children.push(self.parse_parameter_list());
        while self.at_contextual(SyntaxKind::WhereKeyword) {
            children.push(self.parse_type_parameter_constraint_clause());
        }
        children.extend(self.parse_method_body());
        node(SyntaxKind::LocalFunctionStatement, children)
    }

    /// Whether a local variable declaration starts here.
    ///
    /// This is the question `a.b c;` versus `a.b(c);` comes down to, and the
    /// only way to answer it is to read the type and see whether a name and
    /// then a declaration-shaped token follow.
    pub(crate) fn at_local_declaration(&mut self) -> bool {
        if self.at(SyntaxKind::ConstKeyword)
            || (self.at(SyntaxKind::UsingKeyword) && self.nth_kind(1) != SyntaxKind::OpenParenToken)
        {
            return true;
        }
        // `delegate*<void> f = null;` declares a function pointer; a
        // `delegate` without the `*` starts an anonymous method.
        let function_pointer =
            self.at(SyntaxKind::DelegateKeyword) && self.nth_kind(1) == SyntaxKind::AsteriskToken;
        if !self.at(SyntaxKind::IdentifierToken)
            && !is_predefined_type(self.kind())
            && !self.at(SyntaxKind::RefKeyword)
            && !self.at(SyntaxKind::OpenParenToken)
            && !function_pointer
        {
            return false;
        }

        // `await task;` awaits the variable: a type called `await` holding
        // a local called `task` is what it would otherwise read as, and no
        // program names a type that. This parser does not know whether it
        // is inside an async method, so it takes the likely reading.
        if self.at(SyntaxKind::IdentifierToken)
            && self.current_text() == "await"
            && self.nth_kind(1) == SyntaxKind::IdentifierToken
            && self.nth_kind(2) == SyntaxKind::SemicolonToken
        {
            return false;
        }
        self.speculate(|p| {
            if !p.scan_type() {
                return false;
            }
            if !p.at(SyntaxKind::IdentifierToken) {
                return false;
            }
            matches!(
                p.nth_kind(1),
                SyntaxKind::EqualsToken
                    | SyntaxKind::SemicolonToken
                    | SyntaxKind::CommaToken
                    | SyntaxKind::CloseParenToken
                    | SyntaxKind::InKeyword
            )
        })
    }

    fn parse_local_declaration(&mut self) -> GreenElement {
        let mut children = Vec::new();
        while matches!(
            self.kind(),
            SyntaxKind::ConstKeyword | SyntaxKind::UsingKeyword | SyntaxKind::RefKeyword
        ) && !(self.at(SyntaxKind::RefKeyword)
            && self.nth_kind(1) == SyntaxKind::OpenParenToken)
        {
            // `ref` is part of the type of a `ref` local, not a modifier.
            if self.at(SyntaxKind::RefKeyword) {
                break;
            }
            children.push(self.eat_token());
        }
        children.push(self.parse_variable_declaration());
        children.push(self.expect(SyntaxKind::SemicolonToken));
        node(SyntaxKind::LocalDeclarationStatement, children)
    }

    /// `type name = value, other`
    pub(crate) fn parse_variable_declaration(&mut self) -> GreenElement {
        let mut children = vec![self.parse_type()];
        loop {
            children.push(self.parse_variable_declarator());
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        node(SyntaxKind::VariableDeclaration, children)
    }

    fn parse_variable_declarator(&mut self) -> GreenElement {
        let mut children = vec![self.expect_identifier()];
        // `fixed byte buffer[16];` sizes the field here.
        if self.at(SyntaxKind::OpenBracketToken) {
            children.push(self.parse_bracketed_argument_list());
        }
        if let Some(equals) = self.eat_if(SyntaxKind::EqualsToken) {
            let value = self.parse_variable_initializer();
            children.push(node(SyntaxKind::EqualsValueClause, vec![equals, value]));
        }
        node(SyntaxKind::VariableDeclarator, children)
    }
}

/// Puts a keyword in front of a statement that has already been built.
fn prepend(keyword: GreenElement, statement: GreenElement) -> GreenElement {
    match statement.as_node() {
        Some(inner) => {
            let mut children = vec![keyword];
            children.extend(inner.children().iter().cloned());
            node(inner.kind(), children)
        }
        None => statement,
    }
}

/// Whether an expression is `x[]`, parenthesized or not: an indexing with no
/// arguments, which is what an array type reads as where an expression was
/// tried first.
fn indexes_with_nothing(value: &GreenElement) -> bool {
    let Some(node) = value.as_node() else {
        return false;
    };
    match value.kind() {
        SyntaxKind::ParenthesizedExpression => node
            .children()
            .iter()
            .find(|child| child.as_node().is_some())
            .is_some_and(indexes_with_nothing),
        SyntaxKind::ElementAccessExpression => node.children().last().is_some_and(|list| {
            list.kind() == SyntaxKind::BracketedArgumentList
                && list.as_node().is_some_and(|list| {
                    list.children()
                        .iter()
                        .all(|child| child.kind() != SyntaxKind::Argument)
                })
        }),
        _ => false,
    }
}
