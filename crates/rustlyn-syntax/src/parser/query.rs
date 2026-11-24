//! LINQ query expressions.
//!
//! Every keyword here — `from`, `where`, `select` and the rest — is
//! contextual, so `from` only starts a query when a range variable and an `in`
//! follow it. Everything else is an ordinary sub-grammar.

use rustlyn_diagnostics::ErrorCode;

use super::{Parser, node};
use crate::SyntaxKind;
use crate::green::GreenElement;

impl Parser {
    /// Whether `from` here opens a query rather than naming a variable.
    pub(crate) fn at_query_expression(&mut self) -> bool {
        if !self.at_contextual(SyntaxKind::FromKeyword) {
            return false;
        }
        self.speculate(|p| {
            p.eat_token(); // `from`
            if p.at(SyntaxKind::IdentifierToken) && p.nth_kind(1) == SyntaxKind::InKeyword {
                return true;
            }
            if !p.scan_type() || !p.at(SyntaxKind::IdentifierToken) {
                return false;
            }
            p.eat_token();
            p.at(SyntaxKind::InKeyword)
        })
    }

    pub(crate) fn parse_query_expression(&mut self) -> GreenElement {
        self.query_depth += 1;
        let from = self.parse_from_clause();
        let body = self.parse_query_body();
        self.query_depth -= 1;
        node(SyntaxKind::QueryExpression, vec![from, body])
    }

    fn parse_from_clause(&mut self) -> GreenElement {
        let mut children = vec![self.eat_token_as(SyntaxKind::FromKeyword)];
        // `from int x in xs` names the element type; `from x in xs` infers it.
        if !(self.at(SyntaxKind::IdentifierToken) && self.nth_kind(1) == SyntaxKind::InKeyword) {
            children.push(self.parse_type());
        }
        children.push(self.expect_identifier());
        children.push(self.expect(SyntaxKind::InKeyword));
        children.push(self.parse_expression());
        node(SyntaxKind::FromClause, children)
    }

    fn parse_query_body(&mut self) -> GreenElement {
        let mut children = Vec::new();

        loop {
            let before = self.index;
            if self.at_contextual(SyntaxKind::FromKeyword) {
                children.push(self.parse_from_clause());
            } else if self.at_contextual(SyntaxKind::LetKeyword) {
                let keyword = self.eat_token_as(SyntaxKind::LetKeyword);
                let name = self.expect_identifier();
                let equals = self.expect(SyntaxKind::EqualsToken);
                let value = self.parse_expression();
                children.push(node(
                    SyntaxKind::LetClause,
                    vec![keyword, name, equals, value],
                ));
            } else if self.at_contextual(SyntaxKind::WhereKeyword) {
                let keyword = self.eat_token_as(SyntaxKind::WhereKeyword);
                let condition = self.parse_expression();
                children.push(node(SyntaxKind::WhereClause, vec![keyword, condition]));
            } else if self.at_contextual(SyntaxKind::JoinKeyword) {
                children.push(self.parse_join_clause());
            } else if self.at_contextual(SyntaxKind::OrderByKeyword) {
                children.push(self.parse_order_by_clause());
            } else {
                break;
            }
            debug_assert!(self.index > before, "a query clause must consume input");
        }

        children.push(self.parse_select_or_group_clause());

        // `... into g select g` continues the query with a new range variable.
        if self.at_contextual(SyntaxKind::IntoKeyword) {
            let keyword = self.eat_token_as(SyntaxKind::IntoKeyword);
            let name = self.expect_identifier();
            let body = self.parse_query_body();
            children.push(node(
                SyntaxKind::QueryContinuation,
                vec![keyword, name, body],
            ));
        }

        node(SyntaxKind::QueryBody, children)
    }

    fn parse_join_clause(&mut self) -> GreenElement {
        let mut children = vec![self.eat_token_as(SyntaxKind::JoinKeyword)];
        if !(self.at(SyntaxKind::IdentifierToken) && self.nth_kind(1) == SyntaxKind::InKeyword) {
            children.push(self.parse_type());
        }
        children.push(self.expect_identifier());
        children.push(self.expect(SyntaxKind::InKeyword));
        children.push(self.parse_expression());

        children.push(match self.eat_contextual(SyntaxKind::OnKeyword) {
            Some(keyword) => keyword,
            None => {
                self.error_before_current(ErrorCode::ErrSyntaxError, &["on"]);
                Self::missing(SyntaxKind::IdentifierToken)
            }
        });
        children.push(self.parse_expression());

        children.push(match self.eat_contextual(SyntaxKind::EqualsKeyword) {
            Some(keyword) => keyword,
            None => {
                self.error_before_current(ErrorCode::ErrSyntaxError, &["equals"]);
                Self::missing(SyntaxKind::IdentifierToken)
            }
        });
        children.push(self.parse_expression());

        if let Some(keyword) = self.eat_contextual(SyntaxKind::IntoKeyword) {
            let name = self.expect_identifier();
            children.push(node(SyntaxKind::JoinIntoClause, vec![keyword, name]));
        }
        node(SyntaxKind::JoinClause, children)
    }

    fn parse_order_by_clause(&mut self) -> GreenElement {
        let mut children = vec![self.eat_token_as(SyntaxKind::OrderByKeyword)];
        loop {
            let expression = self.parse_expression();
            let (kind, direction) =
                if let Some(keyword) = self.eat_contextual(SyntaxKind::DescendingKeyword) {
                    (SyntaxKind::DescendingOrdering, Some(keyword))
                } else if let Some(keyword) = self.eat_contextual(SyntaxKind::AscendingKeyword) {
                    (SyntaxKind::AscendingOrdering, Some(keyword))
                } else {
                    (SyntaxKind::AscendingOrdering, None)
                };

            let mut ordering = vec![expression];
            ordering.extend(direction);
            children.push(node(kind, ordering));

            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        node(SyntaxKind::OrderByClause, children)
    }

    fn parse_select_or_group_clause(&mut self) -> GreenElement {
        if let Some(keyword) = self.eat_contextual(SyntaxKind::SelectKeyword) {
            let expression = self.parse_expression();
            return node(SyntaxKind::SelectClause, vec![keyword, expression]);
        }
        if let Some(keyword) = self.eat_contextual(SyntaxKind::GroupKeyword) {
            let grouped = self.parse_expression();
            let by = match self.eat_contextual(SyntaxKind::ByKeyword) {
                Some(by) => by,
                None => {
                    self.error_before_current(ErrorCode::ErrSyntaxError, &["by"]);
                    Self::missing(SyntaxKind::IdentifierToken)
                }
            };
            let key = self.parse_expression();
            return node(SyntaxKind::GroupClause, vec![keyword, grouped, by, key]);
        }

        self.error_before_current(ErrorCode::ErrSyntaxError, &["select"]);
        node(
            SyntaxKind::SelectClause,
            vec![
                Self::missing(SyntaxKind::IdentifierToken),
                node(
                    SyntaxKind::IdentifierName,
                    vec![Self::missing(SyntaxKind::IdentifierToken)],
                ),
            ],
        )
    }
}
