//! Declarations: the compilation unit, namespaces, types and their members.
//!
//! Members all start the same way — attributes, modifiers, a type — and only
//! diverge at the name: `(` makes it a method, `{` a property, `this` an
//! indexer, anything else a field. The one case that needs real lookahead is
//! telling a top-level statement from a member, since `int x = 1;` is a local
//! variable at the top of a file and a field inside a class.

use rustlyn_diagnostics::ErrorCode;
use std::sync::Arc;

use super::facts::{
    can_start_expression, is_contextual_modifier, is_predefined_type, is_reserved_modifier,
};
use super::{Parser, node};
use crate::SyntaxKind;
use crate::green::{GreenElement, GreenNode};

/// Where a member is being parsed, which changes what is allowed.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum MemberContext {
    /// Directly in a file, where statements are allowed too.
    TopLevel,
    /// Inside `namespace { }`.
    Namespace,
    /// Inside a type body.
    Type,
}

impl Parser {
    pub(crate) fn parse_compilation_unit(&mut self) -> Arc<GreenNode> {
        let mut children = Vec::new();
        self.parse_extern_aliases(&mut children);
        self.parse_using_directives(&mut children);
        self.parse_members(&mut children, MemberContext::TopLevel);
        // Whatever is left cannot be a declaration, but it is still part of the
        // file and has to stay in the tree.
        if let Some(skipped) = self.skip_tokens(ErrorCode::ErrEofExpected, Self::at_end) {
            children.push(skipped);
        }
        children.extend(self.cut_off());
        children.push(self.end_of_file());
        GreenNode::new(SyntaxKind::CompilationUnit, children)
    }

    fn parse_extern_aliases(&mut self, children: &mut Vec<GreenElement>) {
        while self.at(SyntaxKind::ExternKeyword)
            && self.nth_contextual_kind(1) == SyntaxKind::AliasKeyword
        {
            let keyword = self.eat_token();
            let alias = self.eat_token_as(SyntaxKind::AliasKeyword);
            let name = self.expect_identifier();
            let semicolon = self.expect(SyntaxKind::SemicolonToken);
            children.push(node(
                SyntaxKind::ExternAliasDirective,
                vec![keyword, alias, name, semicolon],
            ));
        }
    }

    fn parse_using_directives(&mut self, children: &mut Vec<GreenElement>) {
        while self.at_using_directive() {
            children.push(self.parse_using_directive());
        }
    }

    /// Whether a `using` directive starts here, as opposed to a `using`
    /// statement or a `using` declaration: `using var a = new D();` and
    /// `using D a = new D();` at the top of a file are a type and then a
    /// name, which no directive is (Roslyn's
    /// `IsPossibleTopLevelUsingLocalDeclarationStatement`). `var` is only a
    /// contextual keyword, so it has to be told apart that way too.
    fn at_using_directive(&mut self) -> bool {
        if self.at_contextual(SyntaxKind::GlobalKeyword)
            && self.nth_kind(1) == SyntaxKind::UsingKeyword
        {
            return true;
        }
        if !self.at(SyntaxKind::UsingKeyword) || self.nth_kind(1) == SyntaxKind::OpenParenToken {
            return false;
        }
        !self.speculate(|p| {
            p.eat_token();
            p.scan_type() && p.at(SyntaxKind::IdentifierToken)
        })
    }

    fn parse_using_directive(&mut self) -> GreenElement {
        let mut children = Vec::new();
        if let Some(global) = self.eat_contextual(SyntaxKind::GlobalKeyword) {
            children.push(global);
        }
        children.push(self.expect(SyntaxKind::UsingKeyword));
        if let Some(keyword) = self.eat_if(SyntaxKind::StaticKeyword) {
            children.push(keyword);
        }
        if let Some(keyword) = self.eat_if(SyntaxKind::UnsafeKeyword) {
            children.push(keyword);
        }
        // `using Alias = Some.Type;`
        if self.at(SyntaxKind::IdentifierToken) && self.nth_kind(1) == SyntaxKind::EqualsToken {
            let name = self.eat_token();
            let equals = self.eat_token();
            children.push(node(SyntaxKind::NameEquals, vec![name, equals]));
            children.push(self.parse_type());
        } else {
            children.push(self.parse_name(false));
        }
        children.push(self.expect(SyntaxKind::SemicolonToken));
        node(SyntaxKind::UsingDirective, children)
    }

    fn parse_members(&mut self, children: &mut Vec<GreenElement>, context: MemberContext) {
        let inside_braces = context != MemberContext::TopLevel;
        loop {
            if self.at_end() {
                break;
            }
            if inside_braces && self.at(SyntaxKind::CloseBraceToken) {
                break;
            }

            // `[assembly: ...]` decorates the output, not whatever follows it,
            // so it hangs off the file rather than off a member.
            if inside_braces.eq(&false) && self.at_global_attribute_list() {
                children.push(self.parse_attribute_list());
                continue;
            }

            let before = self.index;
            let member = self.parse_member_declaration(context);
            if self.index > before {
                children.push(member);
                continue;
            }

            // Nothing was consumed, so `member` is an empty husk: drop it and
            // throw away tokens until something that could start a member
            // turns up, rather than spinning here.
            match self.skip_tokens(ErrorCode::ErrInvalidMemberDecl, |p| {
                (inside_braces && p.at(SyntaxKind::CloseBraceToken)) || p.at_member_start()
            }) {
                Some(skipped) => children.push(skipped),
                None => break,
            }
        }
    }

    /// Whether what starts here, at the top level of a file, is a statement
    /// rather than a member: anything but a type, a namespace, a delegate or
    /// an `extern alias`, once the modifiers in front are looked past.
    fn top_level_statement_ahead(&mut self) -> bool {
        // `extern alias X;` is a directive.
        if self.at(SyntaxKind::ExternKeyword)
            && self.nth_contextual_kind(1) == SyntaxKind::AliasKeyword
        {
            return false;
        }
        self.speculate(|p| {
            let mut modifiers = 0usize;
            while is_reserved_modifier(p.kind())
                || (p.at(SyntaxKind::IdentifierToken)
                    && is_contextual_modifier(p.contextual_kind()))
            {
                // `partial class`, `async void M()`: a modifier only where a
                // declaration follows it; `await x;` or `var partial = 1;`
                // is the identifier it looks like.
                if p.at(SyntaxKind::IdentifierToken)
                    && !matches!(
                        p.nth_kind(1),
                        SyntaxKind::IdentifierToken
                            | SyntaxKind::ClassKeyword
                            | SyntaxKind::StructKeyword
                            | SyntaxKind::InterfaceKeyword
                            | SyntaxKind::EnumKeyword
                            | SyntaxKind::DelegateKeyword
                            | SyntaxKind::VoidKeyword
                    )
                    && !is_predefined_type(p.nth_kind(1))
                    && !is_reserved_modifier(p.nth_kind(1))
                {
                    break;
                }
                p.eat_token();
                modifiers += 1;
            }
            let declares_a_type = matches!(
                p.kind(),
                SyntaxKind::ClassKeyword
                    | SyntaxKind::StructKeyword
                    | SyntaxKind::InterfaceKeyword
                    | SyntaxKind::EnumKeyword
                    | SyntaxKind::NamespaceKeyword
            ) || (p.at(SyntaxKind::DelegateKeyword)
                && p.nth_kind(1) != SyntaxKind::AsteriskToken)
                || (p.at(SyntaxKind::IdentifierToken)
                    && p.contextual_kind() == SyntaxKind::RecordKeyword
                    && matches!(
                        p.nth_kind(1),
                        SyntaxKind::IdentifierToken
                            | SyntaxKind::ClassKeyword
                            | SyntaxKind::StructKeyword
                    ))
                || (p.at(SyntaxKind::IdentifierToken)
                    && p.contextual_kind() == SyntaxKind::ExtensionKeyword
                    && matches!(
                        p.nth_kind(1),
                        SyntaxKind::OpenParenToken | SyntaxKind::LessThanToken
                    ));
            let _ = modifiers;
            !declares_a_type
        })
    }

    /// Whether an `[assembly:` or `[module:` attribute list starts here.
    fn at_global_attribute_list(&self) -> bool {
        self.at(SyntaxKind::OpenBracketToken)
            && matches!(
                self.nth_contextual_kind(1),
                SyntaxKind::AssemblyKeyword | SyntaxKind::ModuleKeyword
            )
            && self.nth_kind(2) == SyntaxKind::ColonToken
    }

    /// Whether the current token could begin a member declaration, which is
    /// where error recovery stops throwing tokens away.
    fn at_member_start(&self) -> bool {
        let kind = self.kind();
        is_reserved_modifier(kind)
            || is_predefined_type(kind)
            || (kind == SyntaxKind::IdentifierToken
                && (is_contextual_modifier(self.contextual_kind())
                    || self.contextual_kind() == SyntaxKind::ExtensionKeyword))
            || matches!(
                kind,
                SyntaxKind::ClassKeyword
                    | SyntaxKind::StructKeyword
                    | SyntaxKind::InterfaceKeyword
                    | SyntaxKind::EnumKeyword
                    | SyntaxKind::DelegateKeyword
                    | SyntaxKind::NamespaceKeyword
                    | SyntaxKind::UsingKeyword
                    | SyntaxKind::EventKeyword
                    | SyntaxKind::OpenBracketToken
                    | SyntaxKind::TildeToken
            )
    }

    fn parse_member_declaration(&mut self, context: MemberContext) -> GreenElement {
        self.enter();
        let member = self.parse_member_declaration_here(context);
        self.leave();
        member
    }

    fn parse_member_declaration_here(&mut self, context: MemberContext) -> GreenElement {
        // `[DoesNotReturn] static void Fail() => …;` at the top of a file is
        // a local function with attributes, as it would be in a method: the
        // statement, attributes and all, is what follows them.
        if context == MemberContext::TopLevel
            && self.at(SyntaxKind::OpenBracketToken)
            && self.speculate(|p| {
                p.parse_attribute_lists();
                !matches!(
                    p.kind(),
                    SyntaxKind::NamespaceKeyword | SyntaxKind::UsingKeyword
                ) && p.top_level_statement_ahead()
            })
        {
            return node(SyntaxKind::GlobalStatement, vec![self.parse_statement()]);
        }
        let attributes = self.parse_attribute_lists();

        if context != MemberContext::Type {
            if self.at(SyntaxKind::NamespaceKeyword) {
                return self.parse_namespace_declaration(attributes);
            }
            if self.at_using_directive() {
                // `[A] using X;`: a directive takes no attributes. They were
                // dropped here once, and every position after them moved —
                // the tree no longer gave its source back. They are kept as a
                // member with nothing after it, and the directive is read on
                // the next turn of the loop.
                if !attributes.is_empty() {
                    let text = self.current_text();
                    self.error_at_current(ErrorCode::ErrInvalidMemberDecl, &[&text]);
                    return node(SyntaxKind::IncompleteMember, attributes);
                }
                return self.parse_using_directive();
            }
        }

        // At the top level of a file, whatever is not a type, a namespace or
        // a `using` is a statement (C# 9): `static int Twice(int x) => …;`
        // is a local function of the program, `int x = 1;` a local, and
        // `await Task.Delay(1);` an `await`.
        if context == MemberContext::TopLevel
            && attributes.is_empty()
            && self.top_level_statement_ahead()
        {
            return node(SyntaxKind::GlobalStatement, vec![self.parse_statement()]);
        }

        let modifiers = self.parse_modifiers_in(context);

        match self.kind() {
            SyntaxKind::ClassKeyword | SyntaxKind::StructKeyword | SyntaxKind::InterfaceKeyword => {
                self.parse_type_declaration(attributes, modifiers)
            }
            SyntaxKind::EnumKeyword => self.parse_enum_declaration(attributes, modifiers),
            // `delegate*<int, void> f;` is a field of function pointer type,
            // not a delegate declaration.
            SyntaxKind::DelegateKeyword if self.nth_kind(1) != SyntaxKind::AsteriskToken => {
                self.parse_delegate_declaration(attributes, modifiers)
            }
            SyntaxKind::TildeToken => self.parse_destructor(attributes, modifiers),
            SyntaxKind::EventKeyword => self.parse_event(attributes, modifiers),
            SyntaxKind::ImplicitKeyword | SyntaxKind::ExplicitKeyword => {
                self.parse_conversion_operator(attributes, modifiers)
            }
            // C# 14: `extension(Receiver) { ... }` groups extension members.
            SyntaxKind::IdentifierToken
                if self.contextual_kind() == SyntaxKind::ExtensionKeyword
                    && matches!(
                        self.nth_kind(1),
                        SyntaxKind::OpenParenToken | SyntaxKind::LessThanToken
                    ) =>
            {
                self.parse_extension_block(attributes, modifiers)
            }
            SyntaxKind::IdentifierToken
                if self.contextual_kind() == SyntaxKind::RecordKeyword
                    && matches!(
                        self.nth_kind(1),
                        SyntaxKind::IdentifierToken
                            | SyntaxKind::ClassKeyword
                            | SyntaxKind::StructKeyword
                    ) =>
            {
                self.parse_record_declaration(attributes, modifiers)
            }
            SyntaxKind::IdentifierToken
                if self.nth_kind(1) == SyntaxKind::OpenParenToken
                    && context == MemberContext::Type =>
            {
                self.parse_constructor(attributes, modifiers)
            }
            _ => {
                // `await Task.Delay(1);` at the top level is a statement
                // (C# 9): `await` is the operator there, whatever it would
                // scan as with a type of that name.
                let awaits = self.at_contextual(SyntaxKind::AwaitKeyword)
                    && can_start_expression(self.nth_kind(1));
                if context == MemberContext::TopLevel
                    && attributes.is_empty()
                    && modifiers.is_empty()
                    && (awaits || !self.scans_as_member(context))
                {
                    return node(SyntaxKind::GlobalStatement, vec![self.parse_statement()]);
                }
                self.parse_member_with_type(attributes, modifiers)
            }
        }
    }

    /// Whether what follows looks like a member rather than a statement.
    ///
    /// At the top of a file `int x = 1;` is a local variable, so a bare name
    /// followed by `=` does not count; inside a type the same text is a field
    /// and does.
    fn scans_as_member(&mut self, context: MemberContext) -> bool {
        if matches!(
            self.kind(),
            SyntaxKind::ClassKeyword
                | SyntaxKind::StructKeyword
                | SyntaxKind::InterfaceKeyword
                | SyntaxKind::EnumKeyword
                | SyntaxKind::NamespaceKeyword
        ) || (self.at(SyntaxKind::DelegateKeyword)
            && self.nth_kind(1) != SyntaxKind::AsteriskToken)
        {
            return true;
        }
        self.speculate(|p| {
            if !p.scan_type() {
                return false;
            }
            if p.at(SyntaxKind::ThisKeyword) {
                return true;
            }
            // Skip an explicit interface qualifier such as `IFoo.`
            while p.at(SyntaxKind::IdentifierToken) && p.nth_kind(1) == SyntaxKind::DotToken {
                p.eat_token();
                p.eat_token();
            }
            if !p.at(SyntaxKind::IdentifierToken) {
                return false;
            }
            p.eat_token();
            let member_only = matches!(
                p.kind(),
                SyntaxKind::OpenParenToken
                    | SyntaxKind::LessThanToken
                    | SyntaxKind::OpenBraceToken
                    | SyntaxKind::EqualsGreaterThanToken
            );
            if member_only {
                return true;
            }
            context != MemberContext::TopLevel
                && matches!(
                    p.kind(),
                    SyntaxKind::SemicolonToken | SyntaxKind::EqualsToken | SyntaxKind::CommaToken
                )
        })
    }

    // -- namespaces and types ---------------------------------------------

    fn parse_namespace_declaration(&mut self, attributes: Vec<GreenElement>) -> GreenElement {
        let mut children = attributes;
        children.push(self.expect(SyntaxKind::NamespaceKeyword));
        children.push(self.parse_name(false));

        // `namespace N;` scopes the rest of the file instead of a block.
        if let Some(semicolon) = self.eat_if(SyntaxKind::SemicolonToken) {
            children.push(semicolon);
            self.parse_extern_aliases(&mut children);
            self.parse_using_directives(&mut children);
            self.parse_members(&mut children, MemberContext::TopLevel);
            return node(SyntaxKind::FileScopedNamespaceDeclaration, children);
        }

        children.push(self.expect(SyntaxKind::OpenBraceToken));
        self.parse_extern_aliases(&mut children);
        self.parse_using_directives(&mut children);
        self.parse_members(&mut children, MemberContext::Namespace);
        children.push(self.expect(SyntaxKind::CloseBraceToken));
        if let Some(semicolon) = self.eat_if(SyntaxKind::SemicolonToken) {
            children.push(semicolon);
        }
        node(SyntaxKind::NamespaceDeclaration, children)
    }

    fn parse_type_declaration(
        &mut self,
        attributes: Vec<GreenElement>,
        modifiers: Vec<GreenElement>,
    ) -> GreenElement {
        let kind = match self.kind() {
            SyntaxKind::ClassKeyword => SyntaxKind::ClassDeclaration,
            SyntaxKind::StructKeyword => SyntaxKind::StructDeclaration,
            _ => SyntaxKind::InterfaceDeclaration,
        };
        let mut children = attributes;
        children.extend(modifiers);
        children.push(self.eat_token());
        children.push(self.expect_identifier());
        if self.at(SyntaxKind::LessThanToken) {
            children.push(self.parse_type_parameter_list());
        }
        if self.at(SyntaxKind::OpenParenToken) {
            children.push(self.parse_parameter_list());
        }
        if self.at(SyntaxKind::ColonToken) {
            children.push(self.parse_base_list());
        }
        while self.at_contextual(SyntaxKind::WhereKeyword) {
            children.push(self.parse_type_parameter_constraint_clause());
        }
        self.parse_type_body(&mut children);
        node(kind, children)
    }

    fn parse_record_declaration(
        &mut self,
        attributes: Vec<GreenElement>,
        modifiers: Vec<GreenElement>,
    ) -> GreenElement {
        let mut children = attributes;
        children.extend(modifiers);
        children.push(self.eat_token_as(SyntaxKind::RecordKeyword));

        let kind = if self.at(SyntaxKind::StructKeyword) {
            children.push(self.eat_token());
            SyntaxKind::RecordStructDeclaration
        } else {
            if let Some(class) = self.eat_if(SyntaxKind::ClassKeyword) {
                children.push(class);
            }
            SyntaxKind::RecordDeclaration
        };

        children.push(self.expect_identifier());
        if self.at(SyntaxKind::LessThanToken) {
            children.push(self.parse_type_parameter_list());
        }
        if self.at(SyntaxKind::OpenParenToken) {
            children.push(self.parse_parameter_list());
        }
        if self.at(SyntaxKind::ColonToken) {
            children.push(self.parse_base_list());
        }
        while self.at_contextual(SyntaxKind::WhereKeyword) {
            children.push(self.parse_type_parameter_constraint_clause());
        }
        self.parse_type_body(&mut children);
        node(kind, children)
    }

    fn parse_extension_block(
        &mut self,
        attributes: Vec<GreenElement>,
        modifiers: Vec<GreenElement>,
    ) -> GreenElement {
        let mut children = attributes;
        children.extend(modifiers);
        children.push(self.eat_token_as(SyntaxKind::ExtensionKeyword));
        if self.at(SyntaxKind::LessThanToken) {
            children.push(self.parse_type_parameter_list());
        }
        let outer = std::mem::replace(&mut self.extension_receiver, true);
        children.push(self.parse_parameter_list());
        self.extension_receiver = outer;
        while self.at_contextual(SyntaxKind::WhereKeyword) {
            children.push(self.parse_type_parameter_constraint_clause());
        }
        self.parse_type_body(&mut children);
        node(SyntaxKind::ExtensionBlockDeclaration, children)
    }

    /// `{ members }` or, for a record without a body, `;`.
    fn parse_type_body(&mut self, children: &mut Vec<GreenElement>) {
        if let Some(semicolon) = self.eat_if(SyntaxKind::SemicolonToken) {
            children.push(semicolon);
            return;
        }
        children.push(self.expect(SyntaxKind::OpenBraceToken));
        self.parse_members(children, MemberContext::Type);
        children.push(self.expect(SyntaxKind::CloseBraceToken));
        if let Some(semicolon) = self.eat_if(SyntaxKind::SemicolonToken) {
            children.push(semicolon);
        }
    }

    fn parse_enum_declaration(
        &mut self,
        attributes: Vec<GreenElement>,
        modifiers: Vec<GreenElement>,
    ) -> GreenElement {
        let mut children = attributes;
        children.extend(modifiers);
        children.push(self.expect(SyntaxKind::EnumKeyword));
        children.push(self.expect_identifier());
        if self.at(SyntaxKind::ColonToken) {
            children.push(self.parse_base_list());
        }
        children.push(self.expect(SyntaxKind::OpenBraceToken));

        while !self.at(SyntaxKind::CloseBraceToken) && !self.at_end() {
            let mut member = self.parse_attribute_lists();
            member.push(self.expect_identifier());
            if let Some(equals) = self.eat_if(SyntaxKind::EqualsToken) {
                let value = self.parse_expression();
                member.push(node(SyntaxKind::EqualsValueClause, vec![equals, value]));
            }
            children.push(node(SyntaxKind::EnumMemberDeclaration, member));
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }

        children.push(self.expect(SyntaxKind::CloseBraceToken));
        if let Some(semicolon) = self.eat_if(SyntaxKind::SemicolonToken) {
            children.push(semicolon);
        }
        node(SyntaxKind::EnumDeclaration, children)
    }

    fn parse_delegate_declaration(
        &mut self,
        attributes: Vec<GreenElement>,
        modifiers: Vec<GreenElement>,
    ) -> GreenElement {
        let mut children = attributes;
        children.extend(modifiers);
        children.push(self.expect(SyntaxKind::DelegateKeyword));
        children.push(self.parse_type());
        children.push(self.expect_identifier());
        if self.at(SyntaxKind::LessThanToken) {
            children.push(self.parse_type_parameter_list());
        }
        children.push(self.parse_parameter_list());
        while self.at_contextual(SyntaxKind::WhereKeyword) {
            children.push(self.parse_type_parameter_constraint_clause());
        }
        children.push(self.expect(SyntaxKind::SemicolonToken));
        node(SyntaxKind::DelegateDeclaration, children)
    }

    // -- members -----------------------------------------------------------

    fn parse_member_with_type(
        &mut self,
        attributes: Vec<GreenElement>,
        modifiers: Vec<GreenElement>,
    ) -> GreenElement {
        let mut children = attributes;
        children.extend(modifiers);
        let ty = self.parse_type();

        if self.at(SyntaxKind::OperatorKeyword) {
            children.push(ty);
            return self.parse_operator(children);
        }

        if self.at(SyntaxKind::ThisKeyword) {
            children.push(ty);
            children.push(self.eat_token());
            children.push(self.parse_bracketed_parameter_list());
            self.parse_accessors_or_arrow(&mut children);
            return node(SyntaxKind::IndexerDeclaration, children);
        }

        children.push(ty);
        let (explicit, identifier) = self.parse_member_name();
        let explicit_operator = explicit.is_some() && self.at(SyntaxKind::OperatorKeyword);
        if let Some(explicit) = explicit {
            children.push(explicit);
        }
        // `static C I<C>.operator +(C a, C b)`, the operator an interface
        // declares implemented explicitly (C# 11), and `void I.operator ++()`
        // (C# 14).
        if explicit_operator {
            return self.parse_operator(children);
        }

        // An explicit interface implementation of an indexer:
        // `int IFoo.this[..]`, where the name is the `this` keyword.
        if self.at(SyntaxKind::OpenBracketToken)
            && (identifier_is_missing(&identifier) || is_this_keyword(&identifier))
        {
            // The `this` keyword is the indexer's name and has to stay in the
            // tree; dropping it was what broke the round trip.
            if is_this_keyword(&identifier) {
                children.push(identifier);
            }
            children.push(self.parse_bracketed_parameter_list());
            self.parse_accessors_or_arrow(&mut children);
            return node(SyntaxKind::IndexerDeclaration, children);
        }

        children.push(identifier);

        if self.at(SyntaxKind::LessThanToken) {
            children.push(self.parse_type_parameter_list());
        }

        if self.at(SyntaxKind::OpenParenToken) {
            children.push(self.parse_parameter_list());
            while self.at_contextual(SyntaxKind::WhereKeyword) {
                children.push(self.parse_type_parameter_constraint_clause());
            }
            children.extend(self.parse_method_body());
            return node(SyntaxKind::MethodDeclaration, children);
        }

        if self.at(SyntaxKind::OpenBraceToken) || self.at(SyntaxKind::EqualsGreaterThanToken) {
            self.parse_accessors_or_arrow(&mut children);
            // `public int X { get; set; } = 0;`
            if let Some(equals) = self.eat_if(SyntaxKind::EqualsToken) {
                let value = self.parse_variable_initializer();
                children.push(node(SyntaxKind::EqualsValueClause, vec![equals, value]));
                children.push(self.expect(SyntaxKind::SemicolonToken));
            }
            return node(SyntaxKind::PropertyDeclaration, children);
        }

        // Anything else is a field: put the type and the name back together
        // into the variable declaration they belong to.
        let identifier = children.pop().expect("the name was just pushed");
        let ty = children.pop().expect("the type was pushed before it");
        let mut declaration = vec![ty, self.finish_variable_declarator(identifier)];
        while let Some(comma) = self.eat_if(SyntaxKind::CommaToken) {
            declaration.push(comma);
            let name = self.expect_identifier();
            declaration.push(self.finish_variable_declarator(name));
        }
        children.push(node(SyntaxKind::VariableDeclaration, declaration));
        children.push(self.expect(SyntaxKind::SemicolonToken));
        node(SyntaxKind::FieldDeclaration, children)
    }

    /// Completes a declarator whose name has already been read.
    fn finish_variable_declarator(&mut self, identifier: GreenElement) -> GreenElement {
        let mut children = vec![identifier];
        if self.at(SyntaxKind::OpenBracketToken) {
            children.push(self.parse_bracketed_argument_list());
        }
        if let Some(equals) = self.eat_if(SyntaxKind::EqualsToken) {
            let value = self.parse_variable_initializer();
            children.push(node(SyntaxKind::EqualsValueClause, vec![equals, value]));
        }
        node(SyntaxKind::VariableDeclarator, children)
    }

    /// Splits `IFoo.Bar` into the interface it implements and the member name.
    fn parse_member_name(&mut self) -> (Option<GreenElement>, GreenElement) {
        let mut qualifier: Option<GreenElement> = None;
        let mut dot: Option<GreenElement> = None;

        while self.at(SyntaxKind::IdentifierToken) {
            let followed_by_dot = self.speculate(|p| {
                p.parse_simple_name(false);
                p.at(SyntaxKind::DotToken)
            });
            if !followed_by_dot {
                break;
            }
            let simple = self.parse_simple_name(false);
            qualifier = Some(match (qualifier, dot.take()) {
                (None, _) => simple,
                (Some(left), Some(separator)) => {
                    node(SyntaxKind::QualifiedName, vec![left, separator, simple])
                }
                (Some(left), None) => left,
            });
            dot = Some(self.eat_token());
        }

        let explicit = match (qualifier, dot) {
            (Some(name), Some(separator)) => Some(node(
                SyntaxKind::ExplicitInterfaceSpecifier,
                vec![name, separator],
            )),
            _ => None,
        };

        // `IFoo.this[int i]` has no identifier of its own, and neither has
        // `I<C>.operator +(…)`: the operator is read by the caller.
        let identifier = if self.at(SyntaxKind::ThisKeyword) {
            self.eat_token()
        } else if explicit.is_some() && self.at(SyntaxKind::OperatorKeyword) {
            Self::missing(SyntaxKind::IdentifierToken)
        } else {
            self.expect_identifier()
        };
        (explicit, identifier)
    }

    fn parse_constructor(
        &mut self,
        attributes: Vec<GreenElement>,
        modifiers: Vec<GreenElement>,
    ) -> GreenElement {
        let mut children = attributes;
        children.extend(modifiers);
        children.push(self.expect_identifier());
        children.push(self.parse_parameter_list());

        if let Some(colon) = self.eat_if(SyntaxKind::ColonToken) {
            let kind = if self.at(SyntaxKind::BaseKeyword) {
                SyntaxKind::BaseConstructorInitializer
            } else {
                SyntaxKind::ThisConstructorInitializer
            };
            // `: this(...)` or `: base(...)`; anything else was taken for the
            // keyword, the end of the file included.
            let keyword = if self.at(SyntaxKind::BaseKeyword) {
                self.eat_token()
            } else {
                self.expect(SyntaxKind::ThisKeyword)
            };
            let arguments = self.parse_argument_list();
            children.push(node(kind, vec![colon, keyword, arguments]));
        }

        children.extend(self.parse_method_body());
        node(SyntaxKind::ConstructorDeclaration, children)
    }

    fn parse_destructor(
        &mut self,
        attributes: Vec<GreenElement>,
        modifiers: Vec<GreenElement>,
    ) -> GreenElement {
        let mut children = attributes;
        children.extend(modifiers);
        children.push(self.expect(SyntaxKind::TildeToken));
        children.push(self.expect_identifier());
        children.push(self.parse_parameter_list());
        children.extend(self.parse_method_body());
        node(SyntaxKind::DestructorDeclaration, children)
    }

    fn parse_operator(&mut self, mut children: Vec<GreenElement>) -> GreenElement {
        children.push(self.expect(SyntaxKind::OperatorKeyword));
        if let Some(checked) = self.eat_if(SyntaxKind::CheckedKeyword) {
            children.push(checked);
        }
        // Any operator token can be overloaded; which ones are legal is a
        // question for the binder.
        children.push(
            if self.kind().is_punctuation()
                || self.at(SyntaxKind::TrueKeyword)
                || self.at(SyntaxKind::FalseKeyword)
            {
                self.eat_token()
            } else {
                let text = self.current_text();
                self.error_at_current(ErrorCode::ErrSyntaxError, &[&text]);
                Self::missing(SyntaxKind::PlusToken)
            },
        );
        children.push(self.parse_parameter_list());
        children.extend(self.parse_method_body());
        node(SyntaxKind::OperatorDeclaration, children)
    }

    fn parse_conversion_operator(
        &mut self,
        attributes: Vec<GreenElement>,
        modifiers: Vec<GreenElement>,
    ) -> GreenElement {
        let mut children = attributes;
        children.extend(modifiers);
        children.push(self.eat_token()); // `implicit` or `explicit`
        // `static explicit IConv<C>.operator int(C c)`: an interface's
        // conversion implemented explicitly (C# 11).
        if self.at(SyntaxKind::IdentifierToken) {
            let (explicit, _) = self.parse_member_name();
            if let Some(explicit) = explicit {
                children.push(explicit);
            }
        }
        children.push(self.expect(SyntaxKind::OperatorKeyword));
        if let Some(checked) = self.eat_if(SyntaxKind::CheckedKeyword) {
            children.push(checked);
        }
        children.push(self.parse_type());
        children.push(self.parse_parameter_list());
        children.extend(self.parse_method_body());
        node(SyntaxKind::ConversionOperatorDeclaration, children)
    }

    fn parse_event(
        &mut self,
        attributes: Vec<GreenElement>,
        modifiers: Vec<GreenElement>,
    ) -> GreenElement {
        let mut children = attributes;
        children.extend(modifiers);
        children.push(self.expect(SyntaxKind::EventKeyword));
        let ty = self.parse_type();

        let (explicit, identifier) = self.parse_member_name();
        // An explicit implementation is never field-like: it has accessors,
        // or — `abstract event Action I1.E;` in an interface (C# 8), which
        // takes `I1.E`'s implementation away again — a `;` where they go.
        if self.at(SyntaxKind::OpenBraceToken) || explicit.is_some() {
            children.push(ty);
            if let Some(explicit) = explicit {
                children.push(explicit);
            }
            children.push(identifier);
            if let Some(semicolon) = self.eat_if(SyntaxKind::SemicolonToken) {
                children.push(semicolon);
            } else {
                children.push(self.parse_accessor_list());
            }
            return node(SyntaxKind::EventDeclaration, children);
        }

        let mut declaration = vec![ty, self.finish_variable_declarator(identifier)];
        while let Some(comma) = self.eat_if(SyntaxKind::CommaToken) {
            declaration.push(comma);
            let name = self.expect_identifier();
            declaration.push(self.finish_variable_declarator(name));
        }
        children.push(node(SyntaxKind::VariableDeclaration, declaration));
        children.push(self.expect(SyntaxKind::SemicolonToken));
        node(SyntaxKind::EventFieldDeclaration, children)
    }

    /// `{ get; set; }` or `=> expression;`
    fn parse_accessors_or_arrow(&mut self, children: &mut Vec<GreenElement>) {
        if self.at(SyntaxKind::EqualsGreaterThanToken) {
            let arrow = self.eat_token();
            let expression = self.parse_expression();
            children.push(node(
                SyntaxKind::ArrowExpressionClause,
                vec![arrow, expression],
            ));
            children.push(self.expect(SyntaxKind::SemicolonToken));
            return;
        }
        children.push(self.parse_accessor_list());
    }

    fn parse_accessor_list(&mut self) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::OpenBraceToken)];
        while !self.at(SyntaxKind::CloseBraceToken) && !self.at_end() {
            let before = self.index;
            children.push(self.parse_accessor());
            if self.index == before {
                break;
            }
        }
        children.push(self.expect(SyntaxKind::CloseBraceToken));
        node(SyntaxKind::AccessorList, children)
    }

    fn parse_accessor(&mut self) -> GreenElement {
        let mut children = self.parse_attribute_lists();
        children.extend(self.parse_accessor_modifiers());

        let (kind, keyword) = match self.contextual_kind() {
            SyntaxKind::GetKeyword => (
                SyntaxKind::GetAccessorDeclaration,
                Some(SyntaxKind::GetKeyword),
            ),
            SyntaxKind::SetKeyword => (
                SyntaxKind::SetAccessorDeclaration,
                Some(SyntaxKind::SetKeyword),
            ),
            SyntaxKind::InitKeyword => (
                SyntaxKind::InitAccessorDeclaration,
                Some(SyntaxKind::InitKeyword),
            ),
            SyntaxKind::AddKeyword => (
                SyntaxKind::AddAccessorDeclaration,
                Some(SyntaxKind::AddKeyword),
            ),
            SyntaxKind::RemoveKeyword => (
                SyntaxKind::RemoveAccessorDeclaration,
                Some(SyntaxKind::RemoveKeyword),
            ),
            _ => (SyntaxKind::UnknownAccessorDeclaration, None),
        };

        match keyword {
            Some(keyword) => children.push(self.eat_token_as(keyword)),
            None => {
                let text = self.current_text();
                self.error_at_current(ErrorCode::ErrSyntaxError, &[&text]);
                return node(kind, children);
            }
        }

        if self.at(SyntaxKind::OpenBraceToken) {
            children.push(self.parse_block());
        } else if self.at(SyntaxKind::EqualsGreaterThanToken) {
            let arrow = self.eat_token();
            let expression = self.parse_expression();
            children.push(node(
                SyntaxKind::ArrowExpressionClause,
                vec![arrow, expression],
            ));
            children.push(self.expect(SyntaxKind::SemicolonToken));
        } else {
            children.push(self.expect(SyntaxKind::SemicolonToken));
        }
        node(kind, children)
    }

    /// A body, an expression body, or just a semicolon.
    pub(crate) fn parse_method_body(&mut self) -> Vec<GreenElement> {
        if self.at(SyntaxKind::OpenBraceToken) {
            let block = self.parse_block();
            let mut body = vec![block];
            if let Some(semicolon) = self.eat_if(SyntaxKind::SemicolonToken) {
                body.push(semicolon);
            }
            return body;
        }
        if self.at(SyntaxKind::EqualsGreaterThanToken) {
            let arrow = self.eat_token();
            let expression = self.parse_expression();
            return vec![
                node(SyntaxKind::ArrowExpressionClause, vec![arrow, expression]),
                self.expect(SyntaxKind::SemicolonToken),
            ];
        }
        vec![self.expect(SyntaxKind::SemicolonToken)]
    }

    // -- modifiers, parameters, attributes --------------------------------

    /// The modifiers of an accessor. Any modifier word is taken, `ref` too,
    /// so that one an accessor cannot have is an error about the accessor
    /// (CS0106) rather than a statement the parser loses its way in.
    fn parse_accessor_modifiers(&mut self) -> Vec<GreenElement> {
        let mut modifiers = Vec::new();
        loop {
            let kind = self.kind();
            if is_reserved_modifier(kind) || kind == SyntaxKind::RefKeyword {
                modifiers.push(self.eat_token());
                continue;
            }
            if kind == SyntaxKind::IdentifierToken && is_contextual_modifier(self.contextual_kind())
            {
                let next = self.nth_kind(1);
                let before_accessor = is_reserved_modifier(next)
                    || next == SyntaxKind::RefKeyword
                    || (next == SyntaxKind::IdentifierToken
                        && (is_contextual_modifier(self.nth_contextual_kind(1))
                            || matches!(
                                self.nth_contextual_kind(1),
                                SyntaxKind::GetKeyword
                                    | SyntaxKind::SetKeyword
                                    | SyntaxKind::InitKeyword
                                    | SyntaxKind::AddKeyword
                                    | SyntaxKind::RemoveKeyword
                            )));
                if before_accessor {
                    let contextual = self.contextual_kind();
                    modifiers.push(self.eat_token_as(contextual));
                    continue;
                }
            }
            break;
        }
        modifiers
    }

    fn parse_modifiers_in(&mut self, context: MemberContext) -> Vec<GreenElement> {
        let mut modifiers = Vec::new();
        loop {
            let kind = self.kind();
            // `new` hides an inherited member, so outside a type body it can
            // only be the operator: `new C(1)` at the top of a file creates an
            // object rather than declaring anything.
            if kind == SyntaxKind::NewKeyword && context != MemberContext::Type {
                break;
            }
            if is_reserved_modifier(kind) {
                // `ref` only modifies a type declaration; in `ref int M()` it
                // belongs to the return type instead.
                if kind == SyntaxKind::RefKeyword && !self.ref_is_a_modifier() {
                    break;
                }
                modifiers.push(self.eat_token());
                continue;
            }
            if kind == SyntaxKind::IdentifierToken
                && is_contextual_modifier(self.contextual_kind())
                && self.contextual_modifier_applies()
            {
                let contextual = self.contextual_kind();
                modifiers.push(self.eat_token_as(contextual));
                continue;
            }
            break;
        }
        modifiers
    }

    fn ref_is_a_modifier(&self) -> bool {
        match self.nth_kind(1) {
            SyntaxKind::StructKeyword => true,
            SyntaxKind::ReadOnlyKeyword => self.nth_kind(2) == SyntaxKind::StructKeyword,
            SyntaxKind::IdentifierToken => {
                self.nth_contextual_kind(1) == SyntaxKind::PartialKeyword
                    && self.nth_kind(2) == SyntaxKind::StructKeyword
            }
            _ => false,
        }
    }

    /// Whether the contextual keyword at the cursor is being used as a
    /// modifier.
    ///
    /// `async` before a type is a modifier; `async` before `=` is a variable.
    fn contextual_modifier_applies(&self) -> bool {
        let next = self.nth_kind(1);
        is_reserved_modifier(next)
            || is_predefined_type(next)
            || is_contextual_modifier(self.nth_contextual_kind(1))
            || matches!(
                next,
                SyntaxKind::ClassKeyword
                    | SyntaxKind::StructKeyword
                    | SyntaxKind::InterfaceKeyword
                    | SyntaxKind::EnumKeyword
                    | SyntaxKind::DelegateKeyword
                    | SyntaxKind::EventKeyword
                    | SyntaxKind::IdentifierToken
            )
    }

    pub(crate) fn parse_parameter_list(&mut self) -> GreenElement {
        self.parse_parameters(
            SyntaxKind::ParameterList,
            SyntaxKind::OpenParenToken,
            SyntaxKind::CloseParenToken,
        )
    }

    fn parse_bracketed_parameter_list(&mut self) -> GreenElement {
        self.parse_parameters(
            SyntaxKind::BracketedParameterList,
            SyntaxKind::OpenBracketToken,
            SyntaxKind::CloseBracketToken,
        )
    }

    fn parse_parameters(
        &mut self,
        kind: SyntaxKind,
        open: SyntaxKind,
        close: SyntaxKind,
    ) -> GreenElement {
        let mut children = vec![self.expect(open)];
        while !self.at(close) && !self.at_end() {
            children.push(self.parse_parameter());
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        children.push(self.expect(close));
        node(kind, children)
    }

    fn parse_parameter(&mut self) -> GreenElement {
        let mut children = self.parse_attribute_lists();
        // `M(int x, __arglist)`: a varargs method's last parameter is the
        // keyword and nothing else.
        if self.at(SyntaxKind::ArgListKeyword) {
            children.push(self.eat_token());
            return node(SyntaxKind::Parameter, children);
        }

        loop {
            let kind = self.kind();
            if matches!(
                kind,
                SyntaxKind::ThisKeyword
                    | SyntaxKind::RefKeyword
                    | SyntaxKind::OutKeyword
                    | SyntaxKind::InKeyword
                    | SyntaxKind::ParamsKeyword
                    | SyntaxKind::ReadOnlyKeyword
            ) {
                children.push(self.eat_token());
                continue;
            }
            if self.at_contextual(SyntaxKind::ScopedKeyword) {
                children.push(self.eat_token_as(SyntaxKind::ScopedKeyword));
                continue;
            }
            break;
        }

        // An extension block names the type it extends and need not name the
        // receiver: `extension(string) { ... }`.
        if (self.extension_receiver
            || !self.at(SyntaxKind::IdentifierToken)
            || self.nth_kind(1) != SyntaxKind::CloseParenToken)
            && self.at_receiver_without_a_name()
        {
            children.push(self.parse_type());
            return node(SyntaxKind::Parameter, children);
        }

        // A lambda parameter may have no type at all: `(x, y) => ...`
        let untyped = self.at(SyntaxKind::IdentifierToken)
            && matches!(
                self.nth_kind(1),
                SyntaxKind::CommaToken
                    | SyntaxKind::CloseParenToken
                    | SyntaxKind::CloseBracketToken
                    | SyntaxKind::EqualsToken
            );
        if !untyped {
            children.push(self.parse_type());
        }
        children.push(self.expect_identifier());

        if let Some(equals) = self.eat_if(SyntaxKind::EqualsToken) {
            let value = self.parse_expression();
            children.push(node(SyntaxKind::EqualsValueClause, vec![equals, value]));
        }
        node(SyntaxKind::Parameter, children)
    }

    /// Whether a type stands alone where a parameter is expected, with no name
    /// after it.
    fn at_receiver_without_a_name(&mut self) -> bool {
        self.speculate(|p| p.scan_type() && p.at(SyntaxKind::CloseParenToken))
    }

    pub(crate) fn parse_type_parameter_list(&mut self) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::LessThanToken)];
        loop {
            let mut parameter = self.parse_attribute_lists();
            if matches!(self.kind(), SyntaxKind::InKeyword | SyntaxKind::OutKeyword) {
                parameter.push(self.eat_token());
            }
            parameter.push(self.expect_identifier());
            children.push(node(SyntaxKind::TypeParameter, parameter));
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        children.push(self.expect(SyntaxKind::GreaterThanToken));
        node(SyntaxKind::TypeParameterList, children)
    }

    pub(crate) fn parse_type_parameter_constraint_clause(&mut self) -> GreenElement {
        let mut children = vec![self.eat_token_as(SyntaxKind::WhereKeyword)];
        children.push(self.expect_identifier());
        children.push(self.expect(SyntaxKind::ColonToken));
        loop {
            children.push(self.parse_type_parameter_constraint());
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        node(SyntaxKind::TypeParameterConstraintClause, children)
    }

    fn parse_type_parameter_constraint(&mut self) -> GreenElement {
        match self.kind() {
            SyntaxKind::NewKeyword => {
                let keyword = self.eat_token();
                let open = self.expect(SyntaxKind::OpenParenToken);
                let close = self.expect(SyntaxKind::CloseParenToken);
                node(
                    SyntaxKind::ConstructorConstraint,
                    vec![keyword, open, close],
                )
            }
            SyntaxKind::ClassKeyword => {
                let mut children = vec![self.eat_token()];
                if let Some(question) = self.eat_if(SyntaxKind::QuestionToken) {
                    children.push(question);
                }
                node(SyntaxKind::ClassConstraint, children)
            }
            SyntaxKind::StructKeyword => node(SyntaxKind::StructConstraint, vec![self.eat_token()]),
            SyntaxKind::DefaultKeyword => {
                node(SyntaxKind::DefaultConstraint, vec![self.eat_token()])
            }
            // C# 13: `where T : allows ref struct`. The clause carries its own
            // comma-separated list, and it always comes last.
            _ if self.at_contextual(SyntaxKind::AllowsKeyword)
                && self.nth_kind(1) == SyntaxKind::RefKeyword =>
            {
                let mut children = vec![self.eat_token_as(SyntaxKind::AllowsKeyword)];
                loop {
                    children.push(node(
                        SyntaxKind::RefStructConstraint,
                        vec![
                            self.expect(SyntaxKind::RefKeyword),
                            self.expect(SyntaxKind::StructKeyword),
                        ],
                    ));
                    match self.eat_if(SyntaxKind::CommaToken) {
                        Some(comma) => children.push(comma),
                        None => break,
                    }
                }
                node(SyntaxKind::AllowsConstraintClause, children)
            }
            _ => node(SyntaxKind::TypeConstraint, vec![self.parse_type()]),
        }
    }

    fn parse_base_list(&mut self) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::ColonToken)];
        loop {
            let ty = self.parse_type();
            // `record Derived(int X) : Base(X)` passes arguments to its base.
            children.push(if self.at(SyntaxKind::OpenParenToken) {
                let arguments = self.parse_argument_list();
                node(SyntaxKind::PrimaryConstructorBaseType, vec![ty, arguments])
            } else {
                node(SyntaxKind::SimpleBaseType, vec![ty])
            });
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        node(SyntaxKind::BaseList, children)
    }

    pub(crate) fn parse_attribute_lists(&mut self) -> Vec<GreenElement> {
        let mut lists = Vec::new();
        while self.at(SyntaxKind::OpenBracketToken) {
            lists.push(self.parse_attribute_list());
        }
        lists
    }

    fn parse_attribute_list(&mut self) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::OpenBracketToken)];

        // `[assembly: X]` and `[return: X]` aim the attribute somewhere else.
        // Any identifier or keyword before a colon is a target as far as the
        // parser is concerned: `[delegate: X]` names no location, and saying
        // so is the binder's business (CS0658), not a syntax error.
        if self.nth_kind(1) == SyntaxKind::ColonToken
            && (self.at(SyntaxKind::IdentifierToken) || self.kind().is_reserved_keyword())
        {
            let target = self.eat_token();
            let colon = self.eat_token();
            children.push(node(
                SyntaxKind::AttributeTargetSpecifier,
                vec![target, colon],
            ));
        }

        while !self.at(SyntaxKind::CloseBracketToken) && !self.at_end() {
            let mut attribute = vec![self.parse_name(false)];
            if self.at(SyntaxKind::OpenParenToken) {
                attribute.push(self.parse_attribute_argument_list());
            }
            children.push(node(SyntaxKind::Attribute, attribute));
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }

        children.push(self.expect(SyntaxKind::CloseBracketToken));
        node(SyntaxKind::AttributeList, children)
    }

    fn parse_attribute_argument_list(&mut self) -> GreenElement {
        let mut children = vec![self.expect(SyntaxKind::OpenParenToken)];
        while !self.at(SyntaxKind::CloseParenToken) && !self.at_end() {
            let mut argument = Vec::new();
            if self.at(SyntaxKind::IdentifierToken) {
                if self.nth_kind(1) == SyntaxKind::EqualsToken {
                    let name = self.eat_token();
                    let equals = self.eat_token();
                    argument.push(node(SyntaxKind::NameEquals, vec![name, equals]));
                } else if self.nth_kind(1) == SyntaxKind::ColonToken {
                    let name = self.eat_token();
                    let colon = self.eat_token();
                    argument.push(node(SyntaxKind::NameColon, vec![name, colon]));
                }
            }
            argument.push(self.parse_expression());
            children.push(node(SyntaxKind::AttributeArgument, argument));
            match self.eat_if(SyntaxKind::CommaToken) {
                Some(comma) => children.push(comma),
                None => break,
            }
        }
        children.push(self.expect(SyntaxKind::CloseParenToken));
        node(SyntaxKind::AttributeArgumentList, children)
    }
}

/// Whether the parser had to invent this identifier.
fn identifier_is_missing(element: &GreenElement) -> bool {
    element.as_token().is_some_and(|token| token.is_missing())
}

/// Whether a member's name is the `this` of an indexer.
fn is_this_keyword(element: &GreenElement) -> bool {
    element
        .as_token()
        .is_some_and(|token| token.kind() == SyntaxKind::ThisKeyword)
}
