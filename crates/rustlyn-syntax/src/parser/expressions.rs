//! Expressions.
//!
//! The binary operators are handled by precedence climbing over the table in
//! [`super::facts`]; everything interesting is in the cases that are not
//! operators at all. `(A)-b` is a subtraction but `(int)-b` is a cast;
//! `x => x` is a lambda but `x` alone is a name; `a < b` is a comparison until
//! a `>` and the token after it prove otherwise. Each of those is settled by
//! parsing ahead and rewinding, which is what C# actually requires.

use rustlyn_diagnostics::ErrorCode;

use super::facts::{
    Precedence, assignment_expression_kind, binary_expression_kind, can_start_expression,
    is_predefined_type, is_right_associative, literal_expression_kind,
    postfix_unary_expression_kind, precedence_of, prefix_unary_expression_kind,
};
use super::types::TypeMode;
use super::{Parser, node};
use crate::SyntaxKind;
use crate::green::GreenElement;

impl Parser {
    pub(crate) fn parse_expression(&mut self) -> GreenElement {
        self.parse_sub_expression(Precedence::Expression)
    }

    /// The expression a pattern may contain.
    ///
    /// A constant pattern stops short of `?:` and the logical operators, so
    /// `x is null ? a : b` is a conditional over a pattern rather than a
    /// pattern that swallowed the whole conditional. Roslyn draws the line in
    /// the same place.
    pub(crate) fn parse_pattern_operand(&mut self) -> GreenElement {
        self.parse_sub_expression(Precedence::Relational)
    }

    /// Parses an expression built from operators that bind at least as tightly
    /// as `min`.
    pub(crate) fn parse_sub_expression(&mut self, min: Precedence) -> GreenElement {
        let mut left = self.parse_unary_expression(min);

        loop {
            let token = self.kind();

            // Assignment is the loosest level and groups to the right, so the
            // recursive call swallows the rest of the chain.
            if let Some(kind) = assignment_expression_kind(token) {
                if min > Precedence::Expression {
                    break;
                }
                let operator = self.eat_token();
                let right = self.parse_sub_expression(Precedence::Expression);
                left = node(kind, vec![left, operator, right]);
                break;
            }

            if let Some(kind) = binary_expression_kind(token) {
                let precedence = precedence_of(kind);
                if precedence < min {
                    break;
                }

                if kind == SyntaxKind::IsExpression {
                    left = self.parse_is(left);
                    continue;
                }

                let operator = self.eat_token();
                let right = if kind == SyntaxKind::AsExpression {
                    self.parse_type_in(TypeMode::Conditional)
                } else if is_right_associative(kind) {
                    self.parse_sub_expression(precedence)
                } else {
                    self.parse_sub_expression(precedence.next())
                };
                left = node(kind, vec![left, operator, right]);
                continue;
            }

            match token {
                SyntaxKind::QuestionToken if min <= Precedence::Conditional => {
                    let question = self.eat_token();
                    let when_true = self.parse_sub_expression(Precedence::Expression);
                    let colon = self.expect(SyntaxKind::ColonToken);
                    let when_false = self.parse_sub_expression(Precedence::Expression);
                    left = node(
                        SyntaxKind::ConditionalExpression,
                        vec![left, question, when_true, colon, when_false],
                    );
                }
                SyntaxKind::DotDotToken if min <= Precedence::Range => {
                    let operator = self.eat_token();
                    let mut children = vec![left, operator];
                    if can_start_expression(self.kind()) {
                        children.push(self.parse_sub_expression(Precedence::Range.next()));
                    }
                    left = node(SyntaxKind::RangeExpression, children);
                }
                SyntaxKind::SwitchKeyword
                    if min <= Precedence::Switch
                        && self.nth_kind(1) == SyntaxKind::OpenBraceToken =>
                {
                    left = self.parse_switch_expression(left);
                }
                _ if min <= Precedence::Switch
                    && self.at_contextual(SyntaxKind::WithKeyword)
                    && self.nth_kind(1) == SyntaxKind::OpenBraceToken =>
                {
                    let keyword = self.eat_token_as(SyntaxKind::WithKeyword);
                    let initializer =
                        self.parse_braced_initializer(SyntaxKind::WithInitializerExpression);
                    left = node(SyntaxKind::WithExpression, vec![left, keyword, initializer]);
                }
                _ => break,
            }
        }

        left
    }

    /// `when condition`, which guards a pattern.
    ///
    /// The condition stops short of lambdas, assignments and conditionals,
    /// because `case X when flag => y` has to leave the `=>` for the arm.
    pub(crate) fn parse_when_clause(&mut self) -> Option<GreenElement> {
        let keyword = self.eat_contextual(SyntaxKind::WhenKeyword)?;
        let condition = self.parse_sub_expression(Precedence::Coalescing);
        Some(node(SyntaxKind::WhenClause, vec![keyword, condition]))
    }

    /// `x is T` and `x is <pattern>` start the same way, so parse the pattern
    /// and look at what came out: a bare type means the type test.
    fn parse_is(&mut self, left: GreenElement) -> GreenElement {
        let keyword = self.eat_token();
        // `is` binds at the relational level, so `x is T | y` is `(x is T) | y`
        // rather than a test against the constant `T | y`.
        let pattern = self.parse_pattern_at(Precedence::Relational);

        if pattern.kind() == SyntaxKind::TypePattern {
            let ty = pattern
                .as_node()
                .expect("a type pattern is a node")
                .children()[0]
                .clone();
            return node(SyntaxKind::IsExpression, vec![left, keyword, ty]);
        }
        node(
            SyntaxKind::IsPatternExpression,
            vec![left, keyword, pattern],
        )
    }

    fn parse_unary_expression(&mut self, min: Precedence) -> GreenElement {
        if self.at_contextual(SyntaxKind::AwaitKeyword) && self.await_is_an_operator() {
            let keyword = self.eat_token_as(SyntaxKind::AwaitKeyword);
            let operand = self.parse_sub_expression(Precedence::Unary);
            return node(SyntaxKind::AwaitExpression, vec![keyword, operand]);
        }

        if let Some(kind) = prefix_unary_expression_kind(self.kind()) {
            let operator = self.eat_token();
            let operand = self.parse_sub_expression(Precedence::Unary);
            return node(kind, vec![operator, operand]);
        }

        if self.at(SyntaxKind::DotDotToken) {
            // `..end` — a range with nothing on the left.
            let operator = self.eat_token();
            let mut children = vec![operator];
            if can_start_expression(self.kind()) {
                children.push(self.parse_sub_expression(Precedence::Range.next()));
            }
            return node(SyntaxKind::RangeExpression, children);
        }

        if self.at(SyntaxKind::ThrowKeyword) {
            let keyword = self.eat_token();
            let operand = self.parse_sub_expression(Precedence::Expression);
            return node(SyntaxKind::ThrowExpression, vec![keyword, operand]);
        }

        // `ref int () => ref x` is a lambda stating a `ref` return type, and
        // not a `ref` of one.
        if self.at(SyntaxKind::RefKeyword)
            && !(min <= Precedence::Expression && self.scans_as_lambda())
        {
            let keyword = self.eat_token();
            let operand = self.parse_sub_expression(Precedence::Expression);
            return node(SyntaxKind::RefExpression, vec![keyword, operand]);
        }

        if self.at(SyntaxKind::OpenParenToken) && self.scans_as_cast() {
            let open = self.eat_token();
            let ty = self.parse_type();
            let close = self.expect(SyntaxKind::CloseParenToken);
            let operand = self.parse_sub_expression(Precedence::Cast);
            return node(SyntaxKind::CastExpression, vec![open, ty, close, operand]);
        }

        let term = self.parse_term(min);
        self.parse_postfix(term)
    }

    /// Whether `await` here is the operator rather than a variable called
    /// `await`.
    ///
    /// Roslyn knows whether it is inside an async method and can answer
    /// exactly; this parser does not track that yet, so it asks whether an
    /// operand follows.
    fn await_is_an_operator(&self) -> bool {
        can_start_expression(self.nth_kind(1))
    }

    /// Whether the parenthesis at the cursor opens a cast.
    ///
    /// `(x)-y` is a subtraction and `(int)-y` is a cast: once the contents are
    /// a type, what decides is the token after the `)`, and for the operators
    /// that can be both prefix and binary, whether the type was a built-in one.
    pub(crate) fn scans_as_cast(&mut self) -> bool {
        // A type read cleanly closes every parenthesis it opens, so the `)`
        // after it is the one closing this `(`, and an operand follows that.
        // Asking first spares reading a type out of every group that could
        // never be one.
        if !self
            .kind_after_closing_paren()
            .is_some_and(can_start_expression)
        {
            return false;
        }
        self.speculate(|p| {
            p.eat_token(); // `(`
            // A type no expression could be: a built-in one, or a function
            // pointer — `(delegate*<void>)&Write` takes an address and
            // casts it.
            let predefined = is_predefined_type(p.kind())
                || (p.at(SyntaxKind::DelegateKeyword)
                    && p.nth_kind(1) == SyntaxKind::AsteriskToken);
            let start = p.index;
            if !p.scan_type() {
                return false;
            }
            // A type that could not be an expression: generic, an array, a
            // nullable or a pointer.
            let written = &p.tokens[start..p.index];
            let decorated = written.iter().any(|token| {
                matches!(
                    token.kind,
                    SyntaxKind::OpenBracketToken
                        | SyntaxKind::QuestionToken
                        | SyntaxKind::AsteriskToken
                )
            });
            let definitely_a_type = predefined
                || decorated
                || written
                    .iter()
                    .any(|token| token.kind == SyntaxKind::LessThanToken);
            if p.eat_if(SyntaxKind::CloseParenToken).is_none() {
                return false;
            }
            if !can_start_expression(p.kind()) {
                return false;
            }
            // `(items)[i]` indexes what `items` holds; only `(int[])[1, 2]`,
            // a type nothing could take for a value, casts a collection
            // expression (Roslyn's `ScanCast`).
            if p.at(SyntaxKind::OpenBracketToken) {
                return definitely_a_type;
            }
            // `+ - & * ^` are prefix operators as well as binary ones, so they
            // only mean a cast when the type could not have been a variable:
            // `(flags) ^ kind` is an exclusive or, not a cast of `^kind`. A
            // pointer, an array or a nullable could not be one either:
            // `*(Options*)&raw` reads `raw` as `Options`.
            if matches!(
                p.kind(),
                SyntaxKind::PlusToken
                    | SyntaxKind::MinusToken
                    | SyntaxKind::AmpersandToken
                    | SyntaxKind::AsteriskToken
                    | SyntaxKind::CaretToken
            ) {
                return predefined || decorated;
            }
            true
        })
    }

    // -- primary expressions ----------------------------------------------

    fn parse_term(&mut self, min: Precedence) -> GreenElement {
        // A lambda binds as loosely as an assignment, so anywhere the caller
        // asked for something tighter, `x => y` cannot be one. That is what
        // leaves the `=>` of a switch arm for the arm to take, and Roslyn
        // draws the line in the same place.
        if min <= Precedence::Expression
            && (self.scans_as_lambda()
                || (self.at(SyntaxKind::OpenBracketToken) && self.scans_as_attributed_lambda()))
        {
            return self.parse_lambda();
        }

        if let Some(kind) = literal_expression_kind(self.kind()) {
            return node(kind, vec![self.eat_token()]);
        }

        match self.kind() {
            // `var (a, b) = pair` declares both names at once.
            // Inside parentheses of its own — `(var(x, y) = 44);` — it is a
            // call of something named `var`: a declaration stands at the
            // start of a statement, or of a `for` or `foreach` header.
            SyntaxKind::IdentifierToken
                if self.at_contextual(SyntaxKind::VarKeyword)
                    && self.nth_kind(1) == SyntaxKind::OpenParenToken
                    && (self.kind_before(1) != SyntaxKind::OpenParenToken
                        || matches!(
                            self.kind_before(2),
                            SyntaxKind::ForKeyword | SyntaxKind::ForEachKeyword
                        ))
                    && self.var_starts_a_deconstruction() =>
            {
                let keyword = self.eat_token();
                let designation = self.parse_variable_designation();
                node(
                    SyntaxKind::DeclarationExpression,
                    vec![node(SyntaxKind::IdentifierName, vec![keyword]), designation],
                )
            }
            // `async delegate { ... }`
            SyntaxKind::IdentifierToken
                if self.at_contextual(SyntaxKind::AsyncKeyword)
                    && self.nth_kind(1) == SyntaxKind::DelegateKeyword =>
            {
                let modifiers = vec![self.eat_token_as(SyntaxKind::AsyncKeyword)];
                self.parse_anonymous_method(modifiers)
            }
            // `static delegate { ... }` and `static async delegate { ... }`
            // (C# 9): a lambda would have been taken above, so what follows
            // the modifiers here is the `delegate` keyword.
            SyntaxKind::StaticKeyword => {
                let mut modifiers = vec![self.eat_token()];
                if self.at_contextual(SyntaxKind::AsyncKeyword)
                    && self.nth_kind(1) == SyntaxKind::DelegateKeyword
                {
                    modifiers.push(self.eat_token_as(SyntaxKind::AsyncKeyword));
                }
                self.parse_anonymous_method(modifiers)
            }
            SyntaxKind::IdentifierToken if self.at_query_expression() => {
                self.parse_query_expression()
            }
            // `global::System.Console` reaches past any alias in scope.
            SyntaxKind::IdentifierToken if self.nth_kind(1) == SyntaxKind::ColonColonToken => {
                let alias = node(SyntaxKind::IdentifierName, vec![self.eat_token()]);
                let colons = self.eat_token();
                let name = self.parse_simple_name(true);
                node(SyntaxKind::AliasQualifiedName, vec![alias, colons, name])
            }
            SyntaxKind::IdentifierToken => self.parse_simple_name(true),
            SyntaxKind::ThisKeyword => node(SyntaxKind::ThisExpression, vec![self.eat_token()]),
            SyntaxKind::BaseKeyword => node(SyntaxKind::BaseExpression, vec![self.eat_token()]),
            // `__arglist` alone is a varargs method's handle on what it was
            // given; `__arglist(a, b)` is what a call gives one.
            SyntaxKind::ArgListKeyword => {
                let keyword = self.eat_token();
                if self.at(SyntaxKind::OpenParenToken) {
                    let arguments = self.parse_argument_list();
                    node(SyntaxKind::ArgListExpression, vec![keyword, arguments])
                } else {
                    node(SyntaxKind::ArgListExpression, vec![keyword])
                }
            }
            SyntaxKind::InterpolatedStringStartToken
            | SyntaxKind::InterpolatedVerbatimStringStartToken
            | SyntaxKind::InterpolatedSingleLineRawStringStartToken
            | SyntaxKind::InterpolatedMultiLineRawStringStartToken => {
                self.parse_interpolated_string()
            }
            SyntaxKind::OpenParenToken => self.parse_parenthesized_or_tuple(),
            SyntaxKind::OpenBracketToken => self.parse_collection_expression(),
            SyntaxKind::NewKeyword => self.parse_new_expression(),
            SyntaxKind::DelegateKeyword => self.parse_anonymous_method(Vec::new()),
            SyntaxKind::StackAllocKeyword => self.parse_stackalloc(),
            SyntaxKind::TypeOfKeyword => self.parse_type_in_parens(SyntaxKind::TypeOfExpression),
            SyntaxKind::SizeOfKeyword => self.parse_type_in_parens(SyntaxKind::SizeOfExpression),
            SyntaxKind::RefTypeKeyword => {
                self.parse_expression_in_parens(SyntaxKind::RefTypeExpression)
            }
            SyntaxKind::MakeRefKeyword => {
                self.parse_expression_in_parens(SyntaxKind::MakeRefExpression)
            }
            SyntaxKind::CheckedKeyword => {
                self.parse_expression_in_parens(SyntaxKind::CheckedExpression)
            }
            SyntaxKind::UncheckedKeyword => {
                self.parse_expression_in_parens(SyntaxKind::UncheckedExpression)
            }
            SyntaxKind::RefValueKeyword => self.parse_ref_value(),
            SyntaxKind::DefaultKeyword => {
                if self.nth_kind(1) == SyntaxKind::OpenParenToken {
                    self.parse_type_in_parens(SyntaxKind::DefaultExpression)
                } else {
                    node(SyntaxKind::DefaultLiteralExpression, vec![self.eat_token()])
                }
            }
            kind if is_predefined_type(kind) => {
                node(SyntaxKind::PredefinedType, vec![self.eat_token()])
            }
            _ => {
                let text = self.current_text();
                self.error_at_current(ErrorCode::ErrInvalidExprTerm, &[&text]);
                node(
                    SyntaxKind::IdentifierName,
                    vec![Self::missing(SyntaxKind::IdentifierToken)],
                )
            }
        }
    }

    /// The suffixes that can follow any primary expression.
    fn parse_postfix(&mut self, mut expression: GreenElement) -> GreenElement {
        loop {
            match self.kind() {
                SyntaxKind::DotToken => {
                    let ends_the_line = self.dot_ends_the_line();
                    let dot = self.eat_token();
                    let name = if ends_the_line {
                        self.missing_name_after_dot()
                    } else {
                        self.parse_simple_name(true)
                    };
                    expression = node(
                        SyntaxKind::SimpleMemberAccessExpression,
                        vec![expression, dot, name],
                    );
                }
                SyntaxKind::MinusGreaterThanToken => {
                    let arrow = self.eat_token();
                    let name = self.parse_simple_name(true);
                    expression = node(
                        SyntaxKind::PointerMemberAccessExpression,
                        vec![expression, arrow, name],
                    );
                }
                // `a?.b` and `a?[i]` guard against null. But since C# 12 gave
                // `[...]` a meaning of its own, `x is null ? [] : y` opens the
                // same way, so a following `:` wins the tie.
                SyntaxKind::QuestionToken
                    if self.nth_kind(1) == SyntaxKind::DotToken
                        || (self.nth_kind(1) == SyntaxKind::OpenBracketToken
                            && !self.question_starts_a_conditional()) =>
                {
                    let question = self.eat_token();
                    let when_not_null = self.parse_binding();
                    expression = node(
                        SyntaxKind::ConditionalAccessExpression,
                        vec![expression, question, when_not_null],
                    );
                }
                SyntaxKind::OpenParenToken => {
                    let arguments = self.parse_argument_list();
                    expression = node(
                        SyntaxKind::InvocationExpression,
                        vec![expression, arguments],
                    );
                }
                SyntaxKind::OpenBracketToken => {
                    let arguments = self.parse_bracketed_argument_list();
                    expression = node(
                        SyntaxKind::ElementAccessExpression,
                        vec![expression, arguments],
                    );
                }
                kind @ (SyntaxKind::PlusPlusToken
                | SyntaxKind::MinusMinusToken
                | SyntaxKind::ExclamationToken) => {
                    let operator = self.eat_token();
                    let node_kind = postfix_unary_expression_kind(kind)
                        .expect("the match arm only lets postfix operators through");
                    expression = node(node_kind, vec![expression, operator]);
                }
                _ => break,
            }
        }
        expression
    }

    /// Whether the `?` at the cursor opens a conditional expression, told by
    /// whether a `:` follows the branch after it.
    fn question_starts_a_conditional(&mut self) -> bool {
        let key = (self.index, self.query_depth, self.pattern_precedence);
        if let Some(&known) = self.conditionals.get(&key) {
            return known;
        }
        let answer = self.speculate(|p| {
            p.eat_token(); // `?`
            p.parse_sub_expression(Precedence::Expression);
            p.at(SyntaxKind::ColonToken)
        });
        self.conditionals.insert(key, answer);
        answer
    }

    /// What follows a `?.` or `?[`, which binds to the same target until the
    /// chain ends.
    fn parse_binding(&mut self) -> GreenElement {
        let binding = if self.at(SyntaxKind::DotToken) {
            let dot = self.eat_token();
            let name = self.parse_simple_name(true);
            node(SyntaxKind::MemberBindingExpression, vec![dot, name])
        } else {
            let arguments = self.parse_bracketed_argument_list();
            node(SyntaxKind::ElementBindingExpression, vec![arguments])
        };
        self.parse_postfix(binding)
    }

    fn parse_parenthesized_or_tuple(&mut self) -> GreenElement {
        // `(int a, string b) = pair;` declares two variables. Only an `=` after
        // the closing parenthesis makes that reading possible, so look for one
        // before allowing declarations inside.
        let deconstruction = self.at_deconstruction_target();
        self.parse_parenthesized_or_tuple_in(deconstruction)
    }

    /// The same, but told from outside whether declarations are allowed, so
    /// that the inner group of `(a, (b, c)) = pair` inherits the answer.
    fn parse_parenthesized_or_tuple_in(&mut self, deconstruction: bool) -> GreenElement {
        // Only a tuple declares: `(var(x, y)) = 10` is a call of something
        // named `var` in parentheses, since one element is only grouping.
        let deconstruction = deconstruction && self.group_has_a_comma();
        let open = self.expect(SyntaxKind::OpenParenToken);
        let first = self.parse_argument_in(deconstruction);

        if !self.at(SyntaxKind::CommaToken) {
            let close = self.expect(SyntaxKind::CloseParenToken);
            // A single unnamed expression in parentheses is just grouping; the
            // argument wrapper would be noise.
            let inner = unwrap_lone_argument(&first);
            return node(
                SyntaxKind::ParenthesizedExpression,
                vec![open, inner, close],
            );
        }

        let mut children = vec![open, first];
        while let Some(comma) = self.eat_if(SyntaxKind::CommaToken) {
            children.push(comma);
            children.push(self.parse_argument_in(deconstruction));
        }
        children.push(self.expect(SyntaxKind::CloseParenToken));
        node(SyntaxKind::TupleExpression, children)
    }

    /// `[1, 2, ..rest]`
    fn parse_collection_expression(&mut self) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::OpenBracketToken)];
        while !self.at(SyntaxKind::CloseBracketToken) && !self.at_end() {
            let element = if self.at(SyntaxKind::DotDotToken) {
                let dots = self.eat_token();
                let value = self.parse_expression();
                node(SyntaxKind::SpreadElement, vec![dots, value])
            } else if self.at_contextual(SyntaxKind::WithKeyword)
                && self.nth_kind(1) == SyntaxKind::OpenParenToken
            {
                // `with(` starting an element is always the arguments of the
                // collection (C# 15), even where it could be read as a call
                // of something named `with`.
                let keyword = self.eat_token_as(SyntaxKind::WithKeyword);
                let arguments = self.parse_argument_list();
                node(SyntaxKind::WithElement, vec![keyword, arguments])
            } else {
                node(SyntaxKind::ExpressionElement, vec![self.parse_expression()])
            };
            children.push(element);
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        children.push(self.expect(SyntaxKind::CloseBracketToken));
        node(SyntaxKind::CollectionExpression, children)
    }

    fn parse_new_expression(&mut self) -> GreenElement {
        let keyword = self.expect(SyntaxKind::NewKeyword);

        // `new { ... }` and `new[] { ... }` leave the type to be inferred.
        if self.at(SyntaxKind::OpenBraceToken) {
            let initializer = self.parse_anonymous_object_initializer();
            return node(
                SyntaxKind::AnonymousObjectCreationExpression,
                vec![keyword, initializer],
            );
        }
        if self.at(SyntaxKind::OpenBracketToken) {
            let rank = self.parse_array_rank_specifier(false);
            let initializer = self.parse_braced_initializer(SyntaxKind::ArrayInitializerExpression);
            return node(
                SyntaxKind::ImplicitArrayCreationExpression,
                vec![keyword, rank, initializer],
            );
        }
        // `new (a, b)` infers the type and passes two arguments; only a `[`
        // after the parentheses makes them a tuple type being arrayed.
        if self.at(SyntaxKind::OpenParenToken) && !self.parens_open_an_array_element_type() {
            let arguments = self.parse_argument_list();
            let mut children = vec![keyword, arguments];
            if self.at(SyntaxKind::OpenBraceToken) {
                children.push(self.parse_object_or_collection_initializer());
            }
            return node(SyntaxKind::ImplicitObjectCreationExpression, children);
        }

        let ty = self.parse_type_without_array_suffix();

        // `new int[3]` is an array creation; `new int[]` needs the ranks too.
        if self.at(SyntaxKind::OpenBracketToken) {
            let mut ranks = Vec::new();
            let mut sizeless = true;
            while self.at(SyntaxKind::OpenBracketToken) {
                sizeless &= matches!(
                    self.nth_kind(1),
                    SyntaxKind::CloseBracketToken | SyntaxKind::CommaToken
                );
                ranks.push(self.parse_array_rank_specifier(true));
            }
            let mut array_type = node(
                SyntaxKind::ArrayType,
                std::iter::once(ty).chain(ranks).collect(),
            );
            // `new object[,]?[] { … }`: an array of nullable arrays, as the
            // type `object[,]?[]` is. Only after ranks without sizes: after
            // `new object[3]`, `?[0]` reads an element of the new array.
            while sizeless
                && self.at(SyntaxKind::QuestionToken)
                && self.nth_kind(1) == SyntaxKind::OpenBracketToken
            {
                let question = self.eat_token();
                let nullable = node(SyntaxKind::NullableType, vec![array_type, question]);
                let mut ranks = Vec::new();
                while self.at(SyntaxKind::OpenBracketToken) {
                    sizeless &= matches!(
                        self.nth_kind(1),
                        SyntaxKind::CloseBracketToken | SyntaxKind::CommaToken
                    );
                    ranks.push(self.parse_array_rank_specifier(true));
                }
                array_type = node(
                    SyntaxKind::ArrayType,
                    std::iter::once(nullable).chain(ranks).collect(),
                );
            }
            let mut children = vec![keyword, array_type];
            if self.at(SyntaxKind::OpenBraceToken) {
                children
                    .push(self.parse_braced_initializer(SyntaxKind::ArrayInitializerExpression));
            }
            return node(SyntaxKind::ArrayCreationExpression, children);
        }

        let mut children = vec![keyword, ty];
        if self.at(SyntaxKind::OpenParenToken) {
            children.push(self.parse_argument_list());
        }
        if self.at(SyntaxKind::OpenBraceToken) {
            children.push(self.parse_object_or_collection_initializer());
        }
        node(SyntaxKind::ObjectCreationExpression, children)
    }

    /// Whether the parentheses after `new` are a tuple type with an array
    /// rank behind them.
    fn parens_open_an_array_element_type(&mut self) -> bool {
        self.speculate(|p| {
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
                    SyntaxKind::EndOfFileToken | SyntaxKind::SemicolonToken => return false,
                    _ => {
                        p.eat_token();
                    }
                }
            }
            p.at(SyntaxKind::OpenBracketToken)
        })
    }

    /// The element type of a `new` expression, stopping before any `[`, which
    /// belongs to the creation rather than to the type.
    fn parse_type_without_array_suffix(&mut self) -> GreenElement {
        let ty = self.parse_element_type_without_array_suffix();
        self.with_pointer_suffix(ty)
    }

    /// `int*` and `delegate*<void>*` where an array's element type is
    /// written: `new int*[3]`, `stackalloc delegate*<int, int>[] { ... }`.
    fn with_pointer_suffix(&mut self, mut ty: GreenElement) -> GreenElement {
        while self.at(SyntaxKind::AsteriskToken) {
            let star = self.eat_token();
            ty = node(SyntaxKind::PointerType, vec![ty, star]);
        }
        ty
    }

    fn parse_element_type_without_array_suffix(&mut self) -> GreenElement {
        // `new (int, string)[0]` creates an array of tuples. The rank belongs
        // to the creation, so the tuple is parsed without type suffixes.
        if self.at(SyntaxKind::OpenParenToken) {
            return self.parse_tuple_type();
        }
        if self.at(SyntaxKind::DelegateKeyword) && self.nth_kind(1) == SyntaxKind::AsteriskToken {
            return self.parse_function_pointer_type();
        }
        if is_predefined_type(self.kind()) {
            let mut ty = node(SyntaxKind::PredefinedType, vec![self.eat_token()]);
            while self.at(SyntaxKind::QuestionToken) {
                let question = self.eat_token();
                ty = node(SyntaxKind::NullableType, vec![ty, question]);
            }
            return ty;
        }
        let mut ty = self.parse_name(false);
        while self.at(SyntaxKind::QuestionToken)
            && !matches!(self.nth_kind(1), SyntaxKind::ColonToken)
        {
            let question = self.eat_token();
            ty = node(SyntaxKind::NullableType, vec![ty, question]);
        }
        ty
    }

    fn parse_stackalloc(&mut self) -> GreenElement {
        let keyword = self.expect(SyntaxKind::StackAllocKeyword);
        if self.at(SyntaxKind::OpenBracketToken) {
            let rank = self.parse_array_rank_specifier(true);
            let initializer = self.parse_braced_initializer(SyntaxKind::ArrayInitializerExpression);
            return node(
                SyntaxKind::ImplicitStackAllocArrayCreationExpression,
                vec![keyword, rank, initializer],
            );
        }
        let ty = self.parse_type_without_array_suffix();
        let mut ranks = Vec::new();
        while self.at(SyntaxKind::OpenBracketToken) {
            ranks.push(self.parse_array_rank_specifier(true));
        }
        let array_type = node(
            SyntaxKind::ArrayType,
            std::iter::once(ty).chain(ranks).collect(),
        );
        let mut children = vec![keyword, array_type];
        if self.at(SyntaxKind::OpenBraceToken) {
            children.push(self.parse_braced_initializer(SyntaxKind::ArrayInitializerExpression));
        }
        node(SyntaxKind::StackAllocArrayCreationExpression, children)
    }

    /// `{ Name = value, ... }` or `{ item, item }` — which one it is depends on
    /// what is inside.
    fn parse_object_or_collection_initializer(&mut self) -> GreenElement {
        // `{ Name = ... }` and `{ ["key"] = ... }` set members; anything else
        // adds elements.
        let object_like = (self.nth_kind(1) == SyntaxKind::IdentifierToken
            && self.nth_kind(2) == SyntaxKind::EqualsToken)
            || self.speculate(|p| {
                p.eat_token();
                p.at(SyntaxKind::OpenBracketToken) && p.brackets_are_a_key()
            });
        let kind = if object_like || self.nth_kind(1) == SyntaxKind::CloseBraceToken {
            SyntaxKind::ObjectInitializerExpression
        } else {
            SyntaxKind::CollectionInitializerExpression
        };
        self.parse_braced_initializer(kind)
    }

    /// `{ 1, 2, 3 }` on the right of an array variable or field.
    pub(crate) fn parse_array_initializer(&mut self) -> GreenElement {
        self.parse_braced_initializer(SyntaxKind::ArrayInitializerExpression)
    }

    /// The right-hand side of an `=`, where an array initializer may stand in
    /// for an expression: `int[] a = { 1, 2 };` and `int[] P { get; } = { 1 };`.
    pub(crate) fn parse_variable_initializer(&mut self) -> GreenElement {
        if self.at(SyntaxKind::OpenBraceToken) {
            self.parse_array_initializer()
        } else {
            self.parse_expression()
        }
    }

    fn parse_braced_initializer(&mut self, kind: SyntaxKind) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::OpenBraceToken)];
        while !self.at(SyntaxKind::CloseBraceToken) && !self.at_end() {
            children.push(if self.at(SyntaxKind::OpenBraceToken) {
                self.parse_braced_initializer(SyntaxKind::ComplexElementInitializerExpression)
            } else if self.at(SyntaxKind::OpenBracketToken) && self.brackets_are_a_key() {
                // `["key"] = value` sets an entry through the indexer. Without
                // the `=` it is a collection expression standing as an element,
                // as in `{ "name", [] }`.
                let key = self.parse_bracketed_argument_list();
                let target = node(SyntaxKind::ImplicitElementAccess, vec![key]);
                let equals = self.expect(SyntaxKind::EqualsToken);
                let value = if self.at(SyntaxKind::OpenBraceToken) {
                    self.parse_object_or_collection_initializer()
                } else {
                    self.parse_expression()
                };
                node(
                    SyntaxKind::SimpleAssignmentExpression,
                    vec![target, equals, value],
                )
            } else if self.at(SyntaxKind::IdentifierToken)
                && self.nth_kind(1) == SyntaxKind::EqualsToken
                && self.nth_kind(2) == SyntaxKind::OpenBraceToken
            {
                // `Member = { ... }` adds to or fills in what the member
                // already holds, rather than assigning a new object to it.
                let name = node(SyntaxKind::IdentifierName, vec![self.eat_token()]);
                let equals = self.eat_token();
                let value = self.parse_object_or_collection_initializer();
                node(
                    SyntaxKind::SimpleAssignmentExpression,
                    vec![name, equals, value],
                )
            } else {
                self.parse_expression()
            });
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        children.push(self.expect(SyntaxKind::CloseBraceToken));
        node(kind, children)
    }

    /// Whether the brackets at the cursor are a dictionary key rather than a
    /// collection expression.
    pub(crate) fn brackets_are_a_key(&mut self) -> bool {
        self.speculate(|p| {
            let mut depth = 0usize;
            // Braces inside the key — `[new C { X = 1 }] = v`, or a lambda
            // body — are part of it, not the end of the initializer.
            let mut braces = 0usize;
            loop {
                match p.kind() {
                    SyntaxKind::OpenBraceToken => {
                        braces += 1;
                        p.eat_token();
                    }
                    SyntaxKind::CloseBraceToken if braces > 0 => {
                        braces -= 1;
                        p.eat_token();
                    }
                    SyntaxKind::SemicolonToken if braces > 0 => {
                        p.eat_token();
                    }
                    SyntaxKind::OpenBracketToken => {
                        depth += 1;
                        p.eat_token();
                    }
                    SyntaxKind::CloseBracketToken => {
                        depth -= 1;
                        p.eat_token();
                        if depth == 0 {
                            break;
                        }
                    }
                    SyntaxKind::EndOfFileToken
                    | SyntaxKind::SemicolonToken
                    | SyntaxKind::CloseBraceToken => return false,
                    _ => {
                        p.eat_token();
                    }
                }
            }
            p.at(SyntaxKind::EqualsToken)
        })
    }

    /// `new { a = 1, x.Y }`
    fn parse_anonymous_object_initializer(&mut self) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::OpenBraceToken)];
        while !self.at(SyntaxKind::CloseBraceToken) && !self.at_end() {
            let mut member = Vec::new();
            if self.at(SyntaxKind::IdentifierToken) && self.nth_kind(1) == SyntaxKind::EqualsToken {
                let name = self.eat_token();
                let equals = self.eat_token();
                member.push(node(SyntaxKind::NameEquals, vec![name, equals]));
            }
            member.push(self.parse_expression());
            children.push(node(SyntaxKind::AnonymousObjectMemberDeclarator, member));
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        children.push(self.expect(SyntaxKind::CloseBraceToken));
        node(SyntaxKind::ObjectInitializerExpression, children)
    }

    fn parse_type_in_parens(&mut self, kind: SyntaxKind) -> GreenElement {
        let keyword = self.eat_token();
        let open = self.expect(SyntaxKind::OpenParenToken);
        let ty = self.parse_type();
        let close = self.expect(SyntaxKind::CloseParenToken);
        node(kind, vec![keyword, open, ty, close])
    }

    fn parse_expression_in_parens(&mut self, kind: SyntaxKind) -> GreenElement {
        let keyword = self.eat_token();
        let open = self.expect(SyntaxKind::OpenParenToken);
        let expression = self.parse_expression();
        let close = self.expect(SyntaxKind::CloseParenToken);
        node(kind, vec![keyword, open, expression, close])
    }

    /// `__refvalue(r, int)`
    fn parse_ref_value(&mut self) -> GreenElement {
        let keyword = self.eat_token();
        let open = self.expect(SyntaxKind::OpenParenToken);
        let expression = self.parse_expression();
        let comma = self.expect(SyntaxKind::CommaToken);
        let ty = self.parse_type();
        let close = self.expect(SyntaxKind::CloseParenToken);
        node(
            SyntaxKind::RefValueExpression,
            vec![keyword, open, expression, comma, ty, close],
        )
    }

    // -- arguments ---------------------------------------------------------

    pub(crate) fn parse_argument_list(&mut self) -> GreenElement {
        self.parse_arguments(
            SyntaxKind::ArgumentList,
            SyntaxKind::OpenParenToken,
            SyntaxKind::CloseParenToken,
        )
    }

    pub(crate) fn parse_bracketed_argument_list(&mut self) -> GreenElement {
        self.parse_arguments(
            SyntaxKind::BracketedArgumentList,
            SyntaxKind::OpenBracketToken,
            SyntaxKind::CloseBracketToken,
        )
    }

    fn parse_arguments(
        &mut self,
        kind: SyntaxKind,
        open: SyntaxKind,
        close: SyntaxKind,
    ) -> GreenElement {
        let mut children = vec![self.expect(open)];
        while !self.at(close) && !self.at_end() {
            children.push(self.parse_argument_in(false));
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        children.push(self.expect(close));
        node(kind, children)
    }

    /// Whether the parentheses at the cursor are the left side of a
    /// deconstruction, which is the only place a bare `(int a, ...)` declares
    /// anything.
    pub(crate) fn at_deconstruction_target(&mut self) -> bool {
        if !self.at(SyntaxKind::OpenParenToken) {
            return false;
        }
        // `skip_group` below ends past the `)` closing this `(`, and only an
        // `=` or `in` there makes a target: most groups are settled by that
        // token without reading them.
        if !matches!(
            self.kind_after_closing_paren(),
            Some(SyntaxKind::EqualsToken | SyntaxKind::InKeyword)
        ) {
            return false;
        }
        self.speculate(|p| {
            // A group with no comma of its own is no tuple: `(var(x, y)) =
            // 42` calls a method named `var`.
            let mut depth = 0usize;
            let mut comma = false;
            let point = p.mark();
            loop {
                match p.kind() {
                    SyntaxKind::OpenParenToken
                    | SyntaxKind::OpenBracketToken
                    | SyntaxKind::OpenBraceToken => depth += 1,
                    SyntaxKind::CloseParenToken
                    | SyntaxKind::CloseBracketToken
                    | SyntaxKind::CloseBraceToken => {
                        depth = depth.saturating_sub(1);
                        if depth == 0 {
                            break;
                        }
                    }
                    SyntaxKind::CommaToken if depth == 1 => comma = true,
                    SyntaxKind::EndOfFileToken | SyntaxKind::SemicolonToken => break,
                    _ => {}
                }
                p.eat_token();
            }
            p.reset(point);
            // `= pair` assigns into it; `in items` is the `foreach` form.
            comma
                && p.skip_group()
                && (p.at(SyntaxKind::EqualsToken) || p.at(SyntaxKind::InKeyword))
        })
    }

    /// Steps over a parenthesized group, nested ones included, and says
    /// whether it closed before the statement did.
    fn skip_group(&mut self) -> bool {
        let mut depth = 0usize;
        loop {
            match self.kind() {
                SyntaxKind::OpenParenToken => {
                    depth += 1;
                    self.eat_token();
                }
                SyntaxKind::CloseParenToken => {
                    depth -= 1;
                    self.eat_token();
                    if depth == 0 {
                        return true;
                    }
                }
                SyntaxKind::EndOfFileToken
                | SyntaxKind::SemicolonToken
                | SyntaxKind::OpenBraceToken => return false,
                _ => {
                    self.eat_token();
                }
            }
        }
    }

    /// Whether the parenthesised group starting here has a comma of its
    /// own, outside anything nested in it.
    fn group_has_a_comma(&mut self) -> bool {
        self.speculate(|p| {
            let mut depth = 0usize;
            loop {
                match p.kind() {
                    SyntaxKind::OpenParenToken
                    | SyntaxKind::OpenBracketToken
                    | SyntaxKind::OpenBraceToken => depth += 1,
                    SyntaxKind::CloseParenToken
                    | SyntaxKind::CloseBracketToken
                    | SyntaxKind::CloseBraceToken => {
                        depth = depth.saturating_sub(1);
                        if depth == 0 {
                            return false;
                        }
                    }
                    SyntaxKind::CommaToken if depth == 1 => return true,
                    SyntaxKind::EndOfFileToken | SyntaxKind::SemicolonToken => return false,
                    _ => {}
                }
                p.eat_token();
            }
        })
    }

    /// `name: ref value`, or just an expression.
    ///
    /// `allow_declaration` opens the door to `int x` naming a new variable,
    /// which is only legal on the left of a deconstruction.
    fn parse_argument_in(&mut self, allow_declaration: bool) -> GreenElement {
        let mut children = Vec::new();

        if self.at(SyntaxKind::IdentifierToken)
            && self.nth_kind(1) == SyntaxKind::ColonToken
            // `a ? b : c` also has a colon, but not right after the name.
            && self.nth_kind(2) != SyntaxKind::ColonToken
        {
            let name = self.eat_token();
            let colon = self.eat_token();
            children.push(node(SyntaxKind::NameColon, vec![name, colon]));
        }

        // `M(ref int () => ref x)` passes a lambda with a `ref` return type,
        // by value.
        let by_reference = matches!(
            self.kind(),
            SyntaxKind::RefKeyword | SyntaxKind::OutKeyword | SyntaxKind::InKeyword
        ) && !(self.at(SyntaxKind::RefKeyword) && self.scans_as_lambda());
        if by_reference {
            children.push(self.eat_token());
        }

        // `out int x` and `out var x` declare the variable in place. Only a
        // by-reference argument can do that, which matters: without the `out`,
        // `M(a < b > c)` is three comparisons, not a declaration of `c`.
        // A nested group inside a deconstruction target is one too — unless
        // it is a tuple type with a name after it: `(int x, (string, long)
        // y) = ...` declares `y`.
        // A group that is only the start of an element — `((b) ? ref x : ref
        // y) = 1` — is an expression like any other.
        if allow_declaration
            && self.at(SyntaxKind::OpenParenToken)
            && !self.at_out_declaration()
            && self.speculate(|p| {
                p.skip_group()
                    && matches!(
                        p.kind(),
                        SyntaxKind::CommaToken | SyntaxKind::CloseParenToken
                    )
            })
        {
            children.push(self.parse_parenthesized_or_tuple_in(true));
            return node(SyntaxKind::Argument, children);
        }
        // `(int x1, var (x2, x3)) = ...`: a `var (…)` inside the target
        // declares its names too, whatever follows the group.
        if allow_declaration
            && self.at_contextual(SyntaxKind::VarKeyword)
            && self.nth_kind(1) == SyntaxKind::OpenParenToken
        {
            let keyword = self.eat_token();
            let designation = self.parse_variable_designation();
            children.push(node(
                SyntaxKind::DeclarationExpression,
                vec![node(SyntaxKind::IdentifierName, vec![keyword]), designation],
            ));
            return node(SyntaxKind::Argument, children);
        }

        if (by_reference || allow_declaration) && self.at_out_declaration() {
            let ty = self.parse_type();
            let designation = self.parse_variable_designation();
            children.push(node(
                SyntaxKind::DeclarationExpression,
                vec![ty, designation],
            ));
        } else {
            children.push(self.parse_expression());
        }

        node(SyntaxKind::Argument, children)
    }

    /// Whether a type and a name follow, as in `out int value`.
    fn at_out_declaration(&mut self) -> bool {
        // A tuple type counts too: `out (int a, string b) pair`.
        if !self.at(SyntaxKind::IdentifierToken)
            && !is_predefined_type(self.kind())
            && !self.at(SyntaxKind::OpenParenToken)
        {
            return false;
        }
        self.speculate(|p| {
            if !p.scan_type() {
                return false;
            }
            // `ia.P[out int x]` declares one in an index as well.
            p.at(SyntaxKind::IdentifierToken)
                && matches!(
                    p.nth_kind(1),
                    SyntaxKind::CommaToken
                        | SyntaxKind::CloseParenToken
                        | SyntaxKind::CloseBracketToken
                )
        })
    }

    // -- lambdas -----------------------------------------------------------

    /// Whether what follows is a lambda rather than a name or a parenthesised
    /// expression.
    ///
    /// The parenthesised form is settled by skipping to the matching `)` and
    /// looking for `=>`; nothing shorter is enough, since `(a, b)` could be a
    /// tuple and `(int x)` could not be anything else.
    fn scans_as_lambda(&mut self) -> bool {
        // `ref int () => ref x` and `delegate*<void> () => ...` state return
        // types that start with a keyword of their own.
        let keyword_type = self.at(SyntaxKind::RefKeyword)
            || (self.at(SyntaxKind::DelegateKeyword)
                && self.nth_kind(1) == SyntaxKind::AsteriskToken);
        if !matches!(
            self.kind(),
            SyntaxKind::IdentifierToken | SyntaxKind::OpenParenToken | SyntaxKind::StaticKeyword
        ) && !is_predefined_type(self.kind())
            && !keyword_type
        {
            return false;
        }

        self.speculate(|p| {
            while p.at(SyntaxKind::StaticKeyword) || p.at_contextual(SyntaxKind::AsyncKeyword) {
                p.eat_token();
            }

            if p.at(SyntaxKind::IdentifierToken)
                && p.nth_kind(1) == SyntaxKind::EqualsGreaterThanToken
            {
                return true;
            }
            // C# 10 lets a lambda state its return type: `void () => ...`.
            // The type is scanned in the mode that leaves a `?` alone when an
            // expression could follow it, so `flag ? (a, b) => x : ...` stays
            // a conditional rather than becoming a lambda returning `flag?`.
            // A type that cannot be a condition, a keyword one or a generic
            // name, makes a `?` after it nullable: `string? () => null`.
            let unambiguous = is_predefined_type(p.kind()) || {
                // `A.B.C<…>`: a dotted name with type arguments.
                let mut at = 0;
                while p.nth_kind(at) == SyntaxKind::IdentifierToken
                    && matches!(
                        p.nth_kind(at + 1),
                        SyntaxKind::DotToken | SyntaxKind::ColonColonToken
                    )
                {
                    at += 2;
                }
                p.nth_kind(at) == SyntaxKind::IdentifierToken
                    && p.nth_kind(at + 1) == SyntaxKind::LessThanToken
            };
            // `(int, int) () => default`: a tuple type, then the parameters.
            if p.at(SyntaxKind::OpenParenToken)
                && p.kind_after_closing_paren() == Some(SyntaxKind::OpenParenToken)
            {
                return p.scan_type_in(TypeMode::Conditional)
                    && p.at(SyntaxKind::OpenParenToken)
                    && p.kind_after_closing_paren() == Some(SyntaxKind::EqualsGreaterThanToken);
            }
            if !p.at(SyntaxKind::OpenParenToken) && !p.scan_type_in(TypeMode::Conditional) {
                return false;
            }
            if unambiguous
                && p.at(SyntaxKind::QuestionToken)
                && p.nth_kind(1) == SyntaxKind::OpenParenToken
            {
                p.eat_token();
            }
            if !p.at(SyntaxKind::OpenParenToken) {
                return false;
            }
            p.kind_after_closing_paren() == Some(SyntaxKind::EqualsGreaterThanToken)
        })
    }

    /// Whether attribute lists and then a lambda follow: `[Pure] static (a,
    /// b) => a + b` (C# 10), as against a collection expression.
    fn scans_as_attributed_lambda(&mut self) -> bool {
        self.speculate(|p| {
            while p.at(SyntaxKind::OpenBracketToken) {
                let mut depth = 0usize;
                loop {
                    match p.kind() {
                        SyntaxKind::OpenBracketToken => {
                            depth += 1;
                            p.eat_token();
                        }
                        SyntaxKind::CloseBracketToken => {
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
            }
            p.scans_as_lambda()
        })
    }

    fn var_starts_a_deconstruction(&mut self) -> bool {
        self.speculate(|p| {
            p.eat_token();
            p.at_deconstruction_target()
        })
    }

    fn parse_lambda(&mut self) -> GreenElement {
        let mut children = self.parse_attribute_lists();
        while self.at(SyntaxKind::StaticKeyword) || self.at_contextual(SyntaxKind::AsyncKeyword) {
            children.push(if self.at(SyntaxKind::StaticKeyword) {
                self.eat_token()
            } else {
                self.eat_token_as(SyntaxKind::AsyncKeyword)
            });
        }

        // An explicit return type comes before the parameter list, so what is
        // here is one unless the lambda starts with `(` or a bare parameter.
        let bare_parameter = self.at(SyntaxKind::IdentifierToken)
            && self.nth_kind(1) == SyntaxKind::EqualsGreaterThanToken;
        // A tuple return type opens with `(` too: `(int, int) () => default`,
        // its parameters after it.
        let tuple_return = self.at(SyntaxKind::OpenParenToken)
            && self.kind_after_closing_paren() == Some(SyntaxKind::OpenParenToken);
        if (!self.at(SyntaxKind::OpenParenToken) || tuple_return) && !bare_parameter {
            let mut ty = self.parse_type_in(TypeMode::Conditional);
            // Known to be a lambda, a `?` before its parameters is the return
            // type's: `string? () => null`.
            if self.at(SyntaxKind::QuestionToken) && self.nth_kind(1) == SyntaxKind::OpenParenToken
            {
                let question = self.eat_token();
                ty = node(SyntaxKind::NullableType, vec![ty, question]);
            }
            children.push(ty);
        }

        let parenthesized = self.at(SyntaxKind::OpenParenToken);
        if parenthesized {
            children.push(self.parse_parameter_list());
        } else {
            let name = self.expect_identifier();
            children.push(node(SyntaxKind::Parameter, vec![name]));
        }

        children.push(self.expect(SyntaxKind::EqualsGreaterThanToken));
        children.push(self.parse_lambda_body());

        node(
            if parenthesized {
                SyntaxKind::ParenthesizedLambdaExpression
            } else {
                SyntaxKind::SimpleLambdaExpression
            },
            children,
        )
    }

    fn parse_lambda_body(&mut self) -> GreenElement {
        if self.at(SyntaxKind::OpenBraceToken) {
            self.parse_block()
        } else {
            self.parse_expression()
        }
    }

    fn parse_anonymous_method(&mut self, modifiers: Vec<GreenElement>) -> GreenElement {
        let mut children = modifiers;
        children.push(self.expect(SyntaxKind::DelegateKeyword));
        if self.at(SyntaxKind::OpenParenToken) {
            children.push(self.parse_parameter_list());
        }
        children.push(self.parse_block());
        node(SyntaxKind::AnonymousMethodExpression, children)
    }

    // -- interpolated strings ----------------------------------------------

    /// `$"a{b,3:N2}c"`
    ///
    /// The lexer has already split this into a start token, text tokens and
    /// ordinary tokens inside the holes, so the expression in a hole is parsed
    /// by the same code as any other expression.
    fn parse_interpolated_string(&mut self) -> GreenElement {
        let mut children = vec![self.eat_token()];
        loop {
            match self.kind() {
                SyntaxKind::InterpolatedStringTextToken => children.push(node(
                    SyntaxKind::InterpolatedStringText,
                    vec![self.eat_token()],
                )),
                SyntaxKind::OpenBraceToken => children.push(self.parse_interpolation()),
                SyntaxKind::InterpolatedStringEndToken
                | SyntaxKind::InterpolatedRawStringEndToken => {
                    children.push(self.eat_token());
                    break;
                }
                _ => {
                    // The string ran off the end of the line or the file; the
                    // lexer has already said so.
                    children.push(Self::missing(SyntaxKind::InterpolatedStringEndToken));
                    break;
                }
            }
        }
        node(SyntaxKind::InterpolatedStringExpression, children)
    }

    fn parse_interpolation(&mut self) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::OpenBraceToken)];
        children.push(self.parse_expression());

        if let Some(comma) = self.eat_if(SyntaxKind::CommaToken) {
            let alignment = self.parse_expression();
            children.push(node(
                SyntaxKind::InterpolationAlignmentClause,
                vec![comma, alignment],
            ));
        }
        if let Some(colon) = self.eat_if(SyntaxKind::ColonToken) {
            let mut format = vec![colon];
            if let Some(text) = self.eat_if(SyntaxKind::InterpolatedStringTextToken) {
                format.push(text);
            }
            children.push(node(SyntaxKind::InterpolationFormatClause, format));
        }

        children.push(self.expect(SyntaxKind::CloseBraceToken));
        node(SyntaxKind::Interpolation, children)
    }

    // -- switch expression -------------------------------------------------

    fn parse_switch_expression(&mut self, governing: GreenElement) -> GreenElement {
        let keyword = self.expect(SyntaxKind::SwitchKeyword);
        let mut children = vec![governing, keyword, self.expect(SyntaxKind::OpenBraceToken)];

        while !self.at(SyntaxKind::CloseBraceToken) && !self.at_end() {
            // An arm's pattern stops short of `=>`, which is why it binds
            // looser than a lambda but tighter than a conditional.
            let mut arm = vec![self.parse_pattern_at(Precedence::Coalescing)];
            if let Some(clause) = self.parse_when_clause() {
                arm.push(clause);
            }
            arm.push(self.expect(SyntaxKind::EqualsGreaterThanToken));
            arm.push(self.parse_expression());
            children.push(node(SyntaxKind::SwitchExpressionArm, arm));

            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }

        children.push(self.expect(SyntaxKind::CloseBraceToken));
        node(SyntaxKind::SwitchExpression, children)
    }
}

/// Takes the expression back out of an `Argument` wrapper when it carries
/// nothing else.
fn unwrap_lone_argument(argument: &GreenElement) -> GreenElement {
    match argument.as_node() {
        Some(node) if node.kind() == SyntaxKind::Argument && node.children().len() == 1 => {
            node.children()[0].clone()
        }
        _ => argument.clone(),
    }
}
