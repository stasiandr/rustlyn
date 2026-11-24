//! Patterns, as they appear after `is`, in `case` labels and in switch
//! expression arms.
//!
//! `or`, `and` and `not` are contextual keywords, so they are recognised by
//! what the identifier spells rather than by its token kind; the three of them
//! form the usual three levels of precedence.

use super::facts::{
    Precedence, binary_expression_kind, can_start_expression, is_predefined_type, precedence_of,
};
use super::types::TypeMode;
use super::{Parser, node};
use crate::SyntaxKind;
use crate::green::GreenElement;

impl Parser {
    pub(crate) fn parse_pattern(&mut self) -> GreenElement {
        // A nested pattern binds as tightly as one in a `case` label, whatever
        // the enclosing pattern was: the operators that could continue it
        // belong to the subpattern, not to what encloses it.
        self.parse_pattern_at(Precedence::Conditional)
    }

    /// Parses a pattern that gives up the input to an operator binding no more
    /// tightly than `min`.
    ///
    /// `x is T | y` is `(x is T) | y`, because `|` binds looser than the
    /// relational level `is` sits at. In a switch arm or a subpattern, where
    /// the pattern binds looser still, the same `|` is part of a constant.
    pub(crate) fn parse_pattern_at(&mut self, min: Precedence) -> GreenElement {
        let outer = std::mem::replace(&mut self.pattern_precedence, min);
        let pattern = self.parse_or_pattern();
        self.pattern_precedence = outer;
        pattern
    }

    fn parse_or_pattern(&mut self) -> GreenElement {
        let mut left = self.parse_and_pattern();
        while self.at_contextual(SyntaxKind::OrKeyword) {
            let operator = self.eat_token_as(SyntaxKind::OrKeyword);
            let right = self.parse_and_pattern();
            left = node(SyntaxKind::OrPattern, vec![left, operator, right]);
        }
        left
    }

    fn parse_and_pattern(&mut self) -> GreenElement {
        let mut left = self.parse_unary_pattern();
        while self.at_contextual(SyntaxKind::AndKeyword) {
            let operator = self.eat_token_as(SyntaxKind::AndKeyword);
            let right = self.parse_unary_pattern();
            left = node(SyntaxKind::AndPattern, vec![left, operator, right]);
        }
        left
    }

    fn parse_unary_pattern(&mut self) -> GreenElement {
        if self.at_contextual(SyntaxKind::NotKeyword) {
            let operator = self.eat_token_as(SyntaxKind::NotKeyword);
            let operand = self.parse_unary_pattern();
            return node(SyntaxKind::NotPattern, vec![operator, operand]);
        }
        self.parse_primary_pattern()
    }

    fn parse_primary_pattern(&mut self) -> GreenElement {
        match self.kind() {
            SyntaxKind::LessThanToken
            | SyntaxKind::LessThanEqualsToken
            | SyntaxKind::GreaterThanToken
            | SyntaxKind::GreaterThanEqualsToken
            | SyntaxKind::EqualsEqualsToken
            | SyntaxKind::ExclamationEqualsToken => {
                let operator = self.eat_token();
                let value = self.parse_relational_operand();
                node(SyntaxKind::RelationalPattern, vec![operator, value])
            }
            SyntaxKind::OpenBracketToken => self.parse_list_pattern(),
            SyntaxKind::DotDotToken => {
                let dots = self.eat_token();
                let mut children = vec![dots];
                if self.at_pattern_start() {
                    children.push(self.parse_pattern());
                }
                node(SyntaxKind::SlicePattern, children)
            }
            SyntaxKind::OpenBraceToken => {
                let clause = self.parse_property_pattern_clause();
                let mut children = vec![clause];
                if self.at_identifier_designation() {
                    children.push(self.parse_variable_designation());
                }
                node(SyntaxKind::RecursivePattern, children)
            }
            // `{ RawKind: (int)SyntaxKind.IsExpression }` matches a constant
            // that happens to be written as a cast.
            SyntaxKind::OpenParenToken if self.scans_as_cast() => node(
                SyntaxKind::ConstantPattern,
                vec![self.parse_pattern_operand()],
            ),
            // Read once however many readings of an enclosing ambiguity ask
            // for it: see `replayed`.
            SyntaxKind::OpenParenToken => {
                self.replayed(Self::parse_parenthesized_or_positional_pattern)
            }
            _ => self.parse_type_or_constant_pattern(),
        }
    }

    /// The right-hand side of `> 0`: a constant, not a full expression, so the
    /// `,` and `=>` that end an arm are left alone.
    fn parse_relational_operand(&mut self) -> GreenElement {
        self.parse_pattern_operand()
    }

    fn parse_list_pattern(&mut self) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::OpenBracketToken)];
        while !self.at(SyntaxKind::CloseBracketToken) && !self.at_end() {
            children.push(self.parse_pattern());
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        children.push(self.expect(SyntaxKind::CloseBracketToken));
        let mut pattern = vec![node(SyntaxKind::ListPattern, children)];
        if self.at_identifier_designation() {
            pattern.push(self.parse_variable_designation());
        }
        if pattern.len() == 1 {
            pattern.pop().expect("just checked the length")
        } else {
            node(SyntaxKind::RecursivePattern, pattern)
        }
    }

    /// `(pattern)` and `(1, 2)` both open the same way; a comma or a `name:`
    /// makes it positional.
    ///
    /// What is inside is read once, and what follows it says what it was.
    /// Reading it once for each question — positional? a pattern that ends at
    /// the parenthesis? — and then again for real made every `(` cost three
    /// readings of everything inside it: fourteen parentheses took eleven
    /// seconds, sixteen more than a minute (found by fuzzing).
    fn parse_parenthesized_or_positional_pattern(&mut self) -> GreenElement {
        // `(int a, int b)` deconstructs, but `(int a, int b)[] xs` is a type:
        // a tuple type stands in a pattern only as an array's element type.
        if self.at_tuple_array_type() {
            let ty = self.parse_type_in(TypeMode::Conditional);
            return self.parse_pattern_after_type(ty);
        }

        // `()` deconstructs into nothing, and `(name: p)` names an element.
        if self.nth_kind(1) == SyntaxKind::CloseParenToken
            || (self.nth_kind(1) == SyntaxKind::IdentifierToken
                && self.nth_kind(2) == SyntaxKind::ColonToken)
        {
            let clause = self.parse_positional_pattern_clause();
            return self.finish_recursive_pattern(clause);
        }

        let start = self.mark();
        let open = self.eat_token(); // `(`
        let before = self.diagnostics.len();
        let first = self.parse_pattern();

        if self.at(SyntaxKind::CommaToken) {
            let mut children = vec![
                open,
                node(SyntaxKind::Subpattern, vec![first]),
                self.eat_token(),
            ];
            while !self.at(SyntaxKind::CloseParenToken) && !self.at_end() {
                children.push(self.parse_subpattern());
                match self.eat_if(SyntaxKind::CommaToken) {
                    Some(comma) => children.push(comma),
                    None => break,
                }
            }
            children.push(self.expect(SyntaxKind::CloseParenToken));
            let clause = node(SyntaxKind::PositionalPatternClause, children);
            return self.finish_recursive_pattern(clause);
        }

        if self.at(SyntaxKind::CloseParenToken) {
            // `(p) name` and `(p) { ... }` deconstruct one element, which is
            // what tells them from a pattern that is merely parenthesised.
            let deconstructs = self.nth_kind(1) == SyntaxKind::OpenBraceToken
                || (self.nth_kind(1) == SyntaxKind::IdentifierToken
                    && self.at_designation_start_at(1));
            if deconstructs {
                let close = self.eat_token();
                let element = node(SyntaxKind::Subpattern, vec![first]);
                let clause = node(
                    SyntaxKind::PositionalPatternClause,
                    vec![open, element, close],
                );
                return self.finish_recursive_pattern(clause);
            }
            if self.diagnostics.len() == before {
                let close = self.eat_token();
                return node(SyntaxKind::ParenthesizedPattern, vec![open, first, close]);
            }
        }

        // `x is 0 or (A | B)` puts a constant in parentheses, not a pattern:
        // `|` means nothing to a pattern, so if the contents do not read as
        // one that ends at the parenthesis, they are an expression.
        self.reset(start);
        node(
            SyntaxKind::ConstantPattern,
            vec![self.parse_pattern_operand()],
        )
    }

    /// What may follow a positional clause: a property clause and a name.
    fn finish_recursive_pattern(&mut self, clause: GreenElement) -> GreenElement {
        let mut children = vec![clause];
        if self.at(SyntaxKind::OpenBraceToken) {
            children.push(self.parse_property_pattern_clause());
        }
        if self.at_identifier_designation() {
            children.push(self.parse_variable_designation());
        }
        node(SyntaxKind::RecursivePattern, children)
    }

    /// Whether a tuple type that an array is made of starts here.
    fn at_tuple_array_type(&mut self) -> bool {
        // The `[` stands after the `)` closing this `(`, since a clean tuple
        // type closes every parenthesis it opens.
        self.at(SyntaxKind::OpenParenToken)
            && self.kind_after_closing_paren() == Some(SyntaxKind::OpenBracketToken)
            && self.speculate(|p| {
                let before = p.diagnostics.len();
                p.parse_tuple_type();
                p.diagnostics.len() == before && p.at(SyntaxKind::OpenBracketToken)
            })
    }

    fn parse_positional_pattern_clause(&mut self) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::OpenParenToken)];
        while !self.at(SyntaxKind::CloseParenToken) && !self.at_end() {
            children.push(self.parse_subpattern());
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        children.push(self.expect(SyntaxKind::CloseParenToken));
        node(SyntaxKind::PositionalPatternClause, children)
    }

    fn parse_property_pattern_clause(&mut self) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::OpenBraceToken)];
        while !self.at(SyntaxKind::CloseBraceToken) && !self.at_end() {
            children.push(self.parse_subpattern());
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        children.push(self.expect(SyntaxKind::CloseBraceToken));
        node(SyntaxKind::PropertyPatternClause, children)
    }

    /// `Name: pattern`, `A.B.C: pattern`, or just `pattern`.
    ///
    /// The dotted form is C# 10's extended property pattern: `{ Type.Name: x }`
    /// saves a nested `{ Type: { Name: x } }`.
    fn parse_subpattern(&mut self) -> GreenElement {
        let mut children = Vec::new();
        if self.at(SyntaxKind::IdentifierToken) {
            if self.nth_kind(1) == SyntaxKind::ColonToken {
                let name = self.eat_token();
                let colon = self.eat_token();
                children.push(node(SyntaxKind::NameColon, vec![name, colon]));
            } else if self.at_property_path() {
                let path = self.parse_property_path();
                let colon = self.expect(SyntaxKind::ColonToken);
                children.push(node(SyntaxKind::ExpressionColon, vec![path, colon]));
            }
        }
        children.push(self.parse_pattern());
        node(SyntaxKind::Subpattern, children)
    }

    /// Whether a dotted name followed by `:` starts here.
    fn at_property_path(&mut self) -> bool {
        self.speculate(|p| {
            p.eat_token();
            while p.at(SyntaxKind::DotToken) && p.nth_kind(1) == SyntaxKind::IdentifierToken {
                p.eat_token();
                p.eat_token();
            }
            p.at(SyntaxKind::ColonToken)
        })
    }

    fn parse_property_path(&mut self) -> GreenElement {
        let mut path = node(SyntaxKind::IdentifierName, vec![self.expect_identifier()]);
        while self.at(SyntaxKind::DotToken) && self.nth_kind(1) == SyntaxKind::IdentifierToken {
            let dot = self.eat_token();
            let name = node(SyntaxKind::IdentifierName, vec![self.eat_token()]);
            path = node(
                SyntaxKind::SimpleMemberAccessExpression,
                vec![path, dot, name],
            );
        }
        path
    }

    fn parse_type_or_constant_pattern(&mut self) -> GreenElement {
        if self.at_contextual(SyntaxKind::VarKeyword) && self.at_designation_start_at(1) {
            let keyword = self.eat_token_as(SyntaxKind::VarKeyword);
            let designation = self.parse_variable_designation();
            return node(SyntaxKind::VarPattern, vec![keyword, designation]);
        }

        if self.at_contextual(SyntaxKind::UnderscoreToken)
            && !matches!(self.nth_kind(1), SyntaxKind::DotToken)
        {
            return node(SyntaxKind::DiscardPattern, vec![self.eat_token()]);
        }

        // `nameof` is a contextual keyword, and an invocation of it is a
        // constant expression rather than a shape to match: `nameof(X.Y)` is
        // the string `"Y"`, not a positional pattern on a type called
        // `nameof`.
        if self.at_contextual(SyntaxKind::NameOfKeyword)
            && self.nth_kind(1) == SyntaxKind::OpenParenToken
        {
            let value = self.parse_sub_expression(self.pattern_precedence);
            return node(SyntaxKind::ConstantPattern, vec![value]);
        }

        // Only something that can be a type is worth trying as one.
        if self.at(SyntaxKind::IdentifierToken) || is_predefined_type(self.kind()) {
            let point = self.mark();
            let before = self.diagnostics.len();
            let ty = self.parse_type_in(TypeMode::Conditional);
            // `float.NaN` reads as a type until the dot, but it is a constant.
            // `two * three` reads as a pointer type and a designation, but a
            // pointer type cannot be matched against; it is a product.
            let a_product =
                ty.kind() == SyntaxKind::PointerType && self.at_identifier_designation();
            if self.diagnostics.len() == before && self.can_follow_type_in_pattern() && !a_product {
                return self.parse_pattern_after_type(ty);
            }
            self.reset(point);
        }

        let value = self.parse_sub_expression(self.pattern_precedence);
        node(SyntaxKind::ConstantPattern, vec![value])
    }

    /// The rest of a pattern once its type has been read: a designation makes
    /// it a declaration, a `(` or `{` makes it recursive, and nothing at all
    /// leaves a bare type test.
    fn parse_pattern_after_type(&mut self, ty: GreenElement) -> GreenElement {
        // A `(` after a type opens a deconstruction, not a designation:
        // `Tests.One(X e)` matches a shape, it does not name a tuple.
        if self.at_identifier_designation() {
            let designation = self.parse_variable_designation();
            return node(SyntaxKind::DeclarationPattern, vec![ty, designation]);
        }
        if self.at(SyntaxKind::OpenParenToken) || self.at(SyntaxKind::OpenBraceToken) {
            let mut children = vec![ty];
            if self.at(SyntaxKind::OpenParenToken) {
                children.push(self.parse_positional_pattern_clause());
            }
            if self.at(SyntaxKind::OpenBraceToken) {
                children.push(self.parse_property_pattern_clause());
            }
            if self.at_identifier_designation() {
                children.push(self.parse_variable_designation());
            }
            return node(SyntaxKind::RecursivePattern, children);
        }
        node(SyntaxKind::TypePattern, vec![ty])
    }

    /// Whether what follows a type leaves it a type, rather than making it the
    /// left operand of an expression that is still going.
    fn can_follow_type_in_pattern(&self) -> bool {
        match self.kind() {
            SyntaxKind::OpenParenToken
            | SyntaxKind::OpenBraceToken
            | SyntaxKind::IdentifierToken
            | SyntaxKind::CloseBraceToken
            | SyntaxKind::CloseBracketToken
            | SyntaxKind::CloseParenToken
            | SyntaxKind::CommaToken
            | SyntaxKind::SemicolonToken => true,
            // `int.MaxValue` reads as a type until the dot, but it is a
            // constant; `x!` and `p->q` are expressions too.
            SyntaxKind::DotToken
            | SyntaxKind::MinusGreaterThanToken
            | SyntaxKind::ExclamationToken => false,
            kind => match binary_expression_kind(kind) {
                // An operator this pattern would not have consumed anyway
                // belongs to whatever encloses the pattern.
                Some(expression) => precedence_of(expression) <= self.pattern_precedence,
                None => true,
            },
        }
    }

    pub(crate) fn parse_variable_designation(&mut self) -> GreenElement {
        if self.at(SyntaxKind::OpenParenToken) {
            let mut children = vec![self.eat_token()];
            while !self.at(SyntaxKind::CloseParenToken) && !self.at_end() {
                children.push(self.parse_variable_designation());
                match self.eat_if(SyntaxKind::CommaToken) {
                    Some(comma) => children.push(comma),
                    None => break,
                }
            }
            children.push(self.expect(SyntaxKind::CloseParenToken));
            return node(SyntaxKind::ParenthesizedVariableDesignation, children);
        }
        if self.at_contextual(SyntaxKind::UnderscoreToken) {
            return node(SyntaxKind::DiscardDesignation, vec![self.eat_token()]);
        }
        node(
            SyntaxKind::SingleVariableDesignation,
            vec![self.expect_identifier()],
        )
    }

    /// Whether a plain name follows, which is the only designation a type can
    /// carry.
    pub(crate) fn at_identifier_designation(&self) -> bool {
        self.nth_kind(0) == SyntaxKind::IdentifierToken && self.at_designation_start_at(0)
    }

    fn at_designation_start_at(&self, offset: usize) -> bool {
        if self.nth_kind(offset) == SyntaxKind::OpenParenToken {
            return true;
        }
        if self.nth_kind(offset) != SyntaxKind::IdentifierToken {
            return false;
        }
        let contextual = self.nth_contextual_kind(offset);

        // `x is A.B or C` names no variable: `or` continues the pattern, and
        // so does `and`.
        if matches!(contextual, SyntaxKind::OrKeyword | SyntaxKind::AndKeyword) {
            return false;
        }
        // `when` usually guards the pattern, but `is bool when` names a
        // variable: the difference is whether a condition follows.
        if contextual == SyntaxKind::WhenKeyword {
            return !can_start_expression(self.nth_kind(offset + 1));
        }
        // Inside a query the query keywords are reserved, so the `select` in
        // `where x is A or B select x` ends the clause rather than naming the
        // result.
        if self.in_query() && is_query_keyword(contextual) {
            return false;
        }
        true
    }

    /// Whether the cursor is inside a query expression.
    pub(super) fn in_query(&self) -> bool {
        self.query_depth > 0
    }

    /// Whether something that could begin a pattern is at the cursor.
    fn at_pattern_start(&self) -> bool {
        !matches!(
            self.kind(),
            SyntaxKind::CloseBracketToken
                | SyntaxKind::CloseParenToken
                | SyntaxKind::CloseBraceToken
                | SyntaxKind::CommaToken
                | SyntaxKind::SemicolonToken
                | SyntaxKind::EqualsGreaterThanToken
                | SyntaxKind::EndOfFileToken
        )
    }
}

/// The contextual keywords a query expression reserves.
pub(super) const fn is_query_keyword(contextual: SyntaxKind) -> bool {
    matches!(
        contextual,
        SyntaxKind::FromKeyword
            | SyntaxKind::WhereKeyword
            | SyntaxKind::SelectKeyword
            | SyntaxKind::GroupKeyword
            | SyntaxKind::IntoKeyword
            | SyntaxKind::OrderByKeyword
            | SyntaxKind::JoinKeyword
            | SyntaxKind::LetKeyword
            | SyntaxKind::OnKeyword
            | SyntaxKind::EqualsKeyword
            | SyntaxKind::ByKeyword
            | SyntaxKind::AscendingKeyword
            | SyntaxKind::DescendingKeyword
    )
}
