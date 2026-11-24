//! Layer 3: the file, and what it declares.
//!
//! This is where guessing stops. An editor that does not want to wait for a
//! compiler finds declarations by their shape — a line that looks like
//! `Type Name(` is a method — and that heuristic is right most of the time
//! and quietly wrong the rest of it: on a `return Foo(x);`, on a LINQ query,
//! on an expression-bodied property, on anything generic enough to have a
//! `<` in it. Being wrong there is not a cosmetic problem, because everything
//! above this layer is built on what it says a file contains.
//!
//! Here the answer comes from the parser instead, so `Type Name(` is a method
//! when the grammar says it is and not when it merely looks like one. The
//! parse costs about twenty microseconds a line, which is too much for a
//! keystroke and nothing at all for a file that was just opened — so it runs
//! once per version of the file, in the background, and is cached against the
//! bytes it was computed from.
//!
//! What comes out is deliberately more than an outline. Each declaration
//! carries the things a navigator needs to follow a name — the type it is
//! declared as, the types of its parameters, the bases it names, its
//! attributes — because collecting them costs one walk here and would cost a
//! second walk later. That is what makes layer 4 a matter of joining files
//! together rather than of reading them again.

use std::sync::Arc;

use rustlyn_syntax::{ParseOptions, SyntaxKind, SyntaxNode, SyntaxTree, parse_with};
use rustlyn_text::{SourceText, TextSpan};

use crate::cache::Cacheable;
use crate::wire::{Reader, Writer};

/// What a declaration declares.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum DeclarationKind {
    Namespace = 0,
    Class = 1,
    Struct = 2,
    Interface = 3,
    Enum = 4,
    Record = 5,
    Delegate = 6,
    Method = 7,
    Constructor = 8,
    Destructor = 9,
    Property = 10,
    Indexer = 11,
    Field = 12,
    Event = 13,
    EnumMember = 14,
    Operator = 15,
    /// A C# 14 `extension` block, which declares no type of its own.
    Extension = 16,
}

impl DeclarationKind {
    #[must_use]
    pub const fn is_type(self) -> bool {
        matches!(
            self,
            Self::Class
                | Self::Struct
                | Self::Interface
                | Self::Enum
                | Self::Record
                | Self::Delegate
        )
    }

    const fn from_byte(byte: u8) -> Option<Self> {
        Some(match byte {
            0 => Self::Namespace,
            1 => Self::Class,
            2 => Self::Struct,
            3 => Self::Interface,
            4 => Self::Enum,
            5 => Self::Record,
            6 => Self::Delegate,
            7 => Self::Method,
            8 => Self::Constructor,
            9 => Self::Destructor,
            10 => Self::Property,
            11 => Self::Indexer,
            12 => Self::Field,
            13 => Self::Event,
            14 => Self::EnumMember,
            15 => Self::Operator,
            16 => Self::Extension,
            _ => return None,
        })
    }
}

/// How a parameter is passed, which is part of what tells two overloads apart.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
#[repr(u8)]
pub enum PassedBy {
    #[default]
    Value = 0,
    Ref = 1,
    Out = 2,
    In = 3,
    /// `this` on the first parameter of an extension method.
    This = 4,
    Params = 5,
}

/// One parameter of a method, indexer or delegate.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Parameter {
    pub name: String,
    /// The type as it is written, which is what a navigator has to resolve.
    pub type_text: String,
    pub passed_by: PassedBy,
    /// Whether the parameter may be left out at the call.
    pub optional: bool,
}

/// One declaration in a file.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Declaration {
    pub name: String,
    pub kind: DeclarationKind,
    /// The word that introduced it: `class`, `record`, `void`, `event`.
    pub keyword: String,
    /// The name's own span, in bytes — where a jump to this lands.
    pub name_span: TextSpan,
    /// The whole declaration, in bytes — what a fold collapses.
    pub full_span: TextSpan,
    pub line: u32,
    /// How deeply nested, for indenting an outline view.
    pub depth: u32,
    /// The type or namespace this sits inside, fully qualified.
    pub container: Option<String>,
    /// A field's or property's type; a method's return type.
    pub type_text: Option<String>,
    /// The bases from `: Base, IFoo`, as written.
    pub bases: Vec<String>,
    /// `Stash<T>` declares `["T"]`.
    pub type_parameters: Vec<String>,
    pub parameters: Vec<Parameter>,
    /// The names of the attributes on it, without the `Attribute` suffix:
    /// `[SerializeField]` is `SerializeField`.
    ///
    /// Kept because the editor above this one has rules that turn on them —
    /// which fields Unity serialises, which methods it calls — and those
    /// rules belong to the editor, not here.
    pub attributes: Vec<String>,
    pub is_static: bool,
    pub is_abstract: bool,
    pub is_override: bool,
    pub is_partial: bool,
}

impl Declaration {
    /// The fully qualified name: the container and the name.
    #[must_use]
    pub fn qualified_name(&self) -> String {
        match &self.container {
            Some(container) if !container.is_empty() => format!("{container}.{}", self.name),
            _ => self.name.clone(),
        }
    }

    /// Whether this is an extension method — a static method whose first
    /// parameter is marked `this`.
    #[must_use]
    pub fn is_extension_method(&self) -> bool {
        self.kind == DeclarationKind::Method
            && self
                .parameters
                .first()
                .is_some_and(|first| first.passed_by == PassedBy::This)
    }
}

/// A `using` at the top of a file.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Using {
    /// The name brought into scope: `System.Collections.Generic`.
    pub name: String,
    /// `using Vec = UnityEngine.Vector3;` has an alias.
    pub alias: Option<String>,
    /// `using static System.Math;`
    pub is_static: bool,
    /// `global using`, which reaches every file in the project.
    pub is_global: bool,
}

/// Everything layer 3 knows about one file.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct FileOutline {
    pub declarations: Vec<Declaration>,
    /// The namespaces declared in this file, fully qualified.
    pub namespaces: Vec<String>,
    pub usings: Vec<Using>,
    /// How many errors the parser reported. Not the errors themselves: the
    /// count is what tells a caller whether to trust the rest, and keeping
    /// the messages would multiply the size of the cache for something the
    /// editor does not show.
    pub parse_errors: u32,
}

impl FileOutline {
    /// Builds the outline of a file.
    #[must_use]
    pub fn of(source: &SourceText, options: &ParseOptions) -> Self {
        Self::of_tree(&parse_with(source.clone(), options))
    }

    /// The same from a tree that has already been parsed.
    #[must_use]
    pub fn of_tree(tree: &SyntaxTree) -> Self {
        let source = SourceHandle(tree);
        let mut outline = Self {
            parse_errors: tree.diagnostics().len() as u32,
            ..Self::default()
        };
        let mut walker = Walker {
            outline: &mut outline,
            tree: source,
        };
        walker.node(&tree.root(), None, 0);
        outline
    }

    /// The types declared here, which is what a project-wide type index is
    /// made of.
    pub fn types(&self) -> impl Iterator<Item = &Declaration> {
        self.declarations
            .iter()
            .filter(|declaration| declaration.kind.is_type())
    }

    /// The declaration whose body contains `offset`, innermost first.
    ///
    /// What a jump bar shows: the class and method the cursor is inside.
    #[must_use]
    pub fn enclosing(&self, offset: u32) -> Vec<&Declaration> {
        let mut found: Vec<&Declaration> = self
            .declarations
            .iter()
            .filter(|declaration| {
                declaration.full_span.start() <= offset && offset < declaration.full_span.end()
            })
            .collect();
        found.sort_by_key(|declaration| std::cmp::Reverse(declaration.depth));
        found
    }
}

/// Borrowed so the walker can reach the text without cloning it.
#[derive(Clone, Copy)]
struct SourceHandle<'a>(&'a SyntaxTree);

impl SourceHandle<'_> {
    /// The text of a span.
    ///
    /// `SyntaxNode::text` would rebuild it from the green tree; slicing the
    /// source is the same answer for a span that came out of it, and is a
    /// memcpy rather than a walk.
    fn text(&self, span: TextSpan) -> String {
        self.0
            .source()
            .get(span)
            .map_or_else(String::new, ToOwned::to_owned)
    }

    fn line_of(&self, offset: u32) -> u32 {
        self.0.source().lines().line_of(offset)
    }
}

struct Walker<'a, 'tree> {
    outline: &'a mut FileOutline,
    tree: SourceHandle<'tree>,
}

impl Walker<'_, '_> {
    /// Walks a node, adding whatever it declares and then its children.
    fn node(&mut self, node: &SyntaxNode, container: Option<&str>, depth: u32) {
        match node.kind() {
            SyntaxKind::CompilationUnit => self.children(node, container, depth),

            SyntaxKind::UsingDirective => self.using(node),

            SyntaxKind::NamespaceDeclaration | SyntaxKind::FileScopedNamespaceDeclaration => {
                let name = self.qualified_name_of(node);
                // A nested `namespace B` inside `namespace A` is `A.B`.
                let full = join(container, &name);
                self.outline.namespaces.push(full.clone());
                if let Some(name_node) = self.name_node(node) {
                    self.push(
                        node,
                        Declaration {
                            name,
                            kind: DeclarationKind::Namespace,
                            keyword: "namespace".into(),
                            name_span: name_node,
                            full_span: node.span(),
                            line: self.tree.line_of(name_node.start()),
                            depth,
                            container: container.map(ToOwned::to_owned),
                            ..blank()
                        },
                    );
                }
                self.children(node, Some(&full), depth + 1);
            }

            kind if is_type_declaration(kind) => self.type_declaration(node, container, depth),

            SyntaxKind::ExtensionBlockDeclaration => {
                // An `extension` block adds members to a type it names; it
                // declares nothing itself, so its members belong to whatever
                // encloses it.
                self.children(node, container, depth);
            }

            SyntaxKind::MethodDeclaration
            | SyntaxKind::ConstructorDeclaration
            | SyntaxKind::DestructorDeclaration
            | SyntaxKind::OperatorDeclaration
            | SyntaxKind::ConversionOperatorDeclaration => {
                self.method(node, container, depth);
            }

            SyntaxKind::PropertyDeclaration | SyntaxKind::EventDeclaration => {
                self.property(node, container, depth);
            }

            SyntaxKind::IndexerDeclaration => self.indexer(node, container, depth),

            SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration => {
                self.field(node, container, depth);
            }

            SyntaxKind::EnumMemberDeclaration => self.enum_member(node, container, depth),

            // Everything else is a statement or an expression: it declares
            // nothing an outline shows, and its children declare nothing
            // either — a local variable is not an outline entry, and a local
            // function belongs to the method it is in.
            _ => {}
        }
    }

    fn children(&mut self, node: &SyntaxNode, container: Option<&str>, depth: u32) {
        for child in node.children() {
            self.node(&child, container, depth);
        }
    }

    fn push(&mut self, _node: &SyntaxNode, declaration: Declaration) {
        self.outline.declarations.push(declaration);
    }

    // MARK: - the kinds of declaration

    fn type_declaration(&mut self, node: &SyntaxNode, container: Option<&str>, depth: u32) {
        let Some(name_span) = self.identifier(node) else {
            return;
        };
        let name = self.tree.text(name_span);
        let kind = type_kind(node.kind());
        let full = join(container, &name);

        let declaration = Declaration {
            name,
            kind,
            keyword: self.leading_keyword(node).unwrap_or_else(|| "class".into()),
            name_span,
            full_span: node.span(),
            line: self.tree.line_of(name_span.start()),
            depth,
            container: container.map(ToOwned::to_owned),
            type_text: None,
            bases: self.bases(node),
            type_parameters: self.type_parameters(node),
            // A record's positional parameters are its constructor's, and are
            // worth having: `record Point(int X, int Y)` declares two of them.
            parameters: self.parameters(node),
            attributes: self.attributes(node),
            is_static: self.has(node, SyntaxKind::StaticKeyword),
            is_abstract: self.has(node, SyntaxKind::AbstractKeyword),
            is_override: false,
            is_partial: self.has_contextual(node, SyntaxKind::PartialKeyword),
        };
        self.push(node, declaration);

        // A delegate has no body, so it has no members to walk into.
        if kind != DeclarationKind::Delegate {
            self.children(node, Some(&full), depth + 1);
        }
    }

    fn method(&mut self, node: &SyntaxNode, container: Option<&str>, depth: u32) {
        // A constructor's name is its identifier; an operator's is the
        // operator token, which the grammar puts where the name goes.
        let name_span = self.identifier(node).or_else(|| self.operator_name(node));
        let Some(name_span) = name_span else { return };

        let kind = match node.kind() {
            SyntaxKind::ConstructorDeclaration => DeclarationKind::Constructor,
            SyntaxKind::DestructorDeclaration => DeclarationKind::Destructor,
            SyntaxKind::OperatorDeclaration | SyntaxKind::ConversionOperatorDeclaration => {
                DeclarationKind::Operator
            }
            _ => DeclarationKind::Method,
        };

        let type_text = self.return_type(node);
        self.push(
            node,
            Declaration {
                name: self.tree.text(name_span),
                kind,
                keyword: type_text.clone().unwrap_or_else(|| "void".into()),
                name_span,
                full_span: node.span(),
                line: self.tree.line_of(name_span.start()),
                depth,
                container: container.map(ToOwned::to_owned),
                type_text,
                bases: Vec::new(),
                type_parameters: self.type_parameters(node),
                parameters: self.parameters(node),
                attributes: self.attributes(node),
                is_static: self.has(node, SyntaxKind::StaticKeyword),
                is_abstract: self.has(node, SyntaxKind::AbstractKeyword),
                is_override: self.has(node, SyntaxKind::OverrideKeyword),
                is_partial: self.has_contextual(node, SyntaxKind::PartialKeyword),
            },
        );
    }

    fn property(&mut self, node: &SyntaxNode, container: Option<&str>, depth: u32) {
        let Some(name_span) = self.identifier(node) else {
            return;
        };
        let type_text = self.return_type(node);
        let kind = if node.kind() == SyntaxKind::EventDeclaration {
            DeclarationKind::Event
        } else {
            DeclarationKind::Property
        };
        self.push(
            node,
            Declaration {
                name: self.tree.text(name_span),
                kind,
                keyword: type_text.clone().unwrap_or_default(),
                name_span,
                full_span: node.span(),
                line: self.tree.line_of(name_span.start()),
                depth,
                container: container.map(ToOwned::to_owned),
                type_text,
                attributes: self.attributes(node),
                is_static: self.has(node, SyntaxKind::StaticKeyword),
                is_abstract: self.has(node, SyntaxKind::AbstractKeyword),
                is_override: self.has(node, SyntaxKind::OverrideKeyword),
                ..blank()
            },
        );
    }

    fn indexer(&mut self, node: &SyntaxNode, container: Option<&str>, depth: u32) {
        // An indexer is named `this`, and that is the token to jump to.
        let Some(this) = node.child_token_of_kind(SyntaxKind::ThisKeyword) else {
            return;
        };
        let type_text = self.return_type(node);
        self.push(
            node,
            Declaration {
                name: "this[]".into(),
                kind: DeclarationKind::Indexer,
                keyword: type_text.clone().unwrap_or_default(),
                name_span: this.span(),
                full_span: node.span(),
                line: self.tree.line_of(this.span().start()),
                depth,
                container: container.map(ToOwned::to_owned),
                type_text,
                parameters: self.parameters(node),
                attributes: self.attributes(node),
                is_static: false,
                ..blank()
            },
        );
    }

    /// A field declares one entry per name: `int a, b;` declares two.
    fn field(&mut self, node: &SyntaxNode, container: Option<&str>, depth: u32) {
        let Some(variables) = node.child_of_kind(SyntaxKind::VariableDeclaration) else {
            return;
        };
        let type_text = variables
            .children()
            .find(|child| child.kind().is_type_node())
            .map(|node| self.tree.text(node.span()));
        let kind = if node.kind() == SyntaxKind::EventFieldDeclaration {
            DeclarationKind::Event
        } else {
            DeclarationKind::Field
        };
        let attributes = self.attributes(node);
        let is_static = self.has(node, SyntaxKind::StaticKeyword);

        for declarator in variables
            .children()
            .filter(|child| child.kind() == SyntaxKind::VariableDeclarator)
        {
            let Some(name) = declarator.child_token_of_kind(SyntaxKind::IdentifierToken) else {
                continue;
            };
            let name_span = name.span();
            self.push(
                node,
                Declaration {
                    name: self.tree.text(name_span),
                    kind,
                    keyword: type_text.clone().unwrap_or_default(),
                    name_span,
                    full_span: node.span(),
                    line: self.tree.line_of(name_span.start()),
                    depth,
                    container: container.map(ToOwned::to_owned),
                    type_text: type_text.clone(),
                    attributes: attributes.clone(),
                    is_static,
                    ..blank()
                },
            );
        }
    }

    fn enum_member(&mut self, node: &SyntaxNode, container: Option<&str>, depth: u32) {
        let Some(name_span) = self.identifier(node) else {
            return;
        };
        self.push(
            node,
            Declaration {
                name: self.tree.text(name_span),
                kind: DeclarationKind::EnumMember,
                keyword: String::new(),
                name_span,
                full_span: node.span(),
                line: self.tree.line_of(name_span.start()),
                depth,
                container: container.map(ToOwned::to_owned),
                type_text: container.map(ToOwned::to_owned),
                attributes: self.attributes(node),
                ..blank()
            },
        );
    }

    fn using(&mut self, node: &SyntaxNode) {
        let alias = node
            .child_of_kind(SyntaxKind::NameEquals)
            .and_then(|equals| equals.child_token_of_kind(SyntaxKind::IdentifierToken))
            .map(|token| self.tree.text(token.span()));
        let Some(name) = node
            .children()
            .find(|child| child.kind().is_type_node())
            .map(|node| self.tree.text(node.span()))
        else {
            return;
        };
        self.outline.usings.push(Using {
            name,
            alias,
            is_static: node
                .child_token_of_kind(SyntaxKind::StaticKeyword)
                .is_some(),
            is_global: node
                .child_tokens()
                .any(|token| token.contextual_kind() == SyntaxKind::GlobalKeyword),
        });
    }

    // MARK: - reading the pieces

    fn identifier(&self, node: &SyntaxNode) -> Option<TextSpan> {
        node.child_token_of_kind(SyntaxKind::IdentifierToken)
            .filter(|token| !token.is_missing())
            .map(|token| token.span())
    }

    /// The name of an operator, which stands where an identifier would.
    fn operator_name(&self, node: &SyntaxNode) -> Option<TextSpan> {
        let operator = node.child_token_of_kind(SyntaxKind::OperatorKeyword)?;
        // `operator +` — the token after the keyword is the name.
        let after = node
            .child_tokens()
            .find(|token| token.span().start() > operator.span().start())?;
        Some(after.span())
    }

    /// The word that introduces a declaration, for showing in an outline.
    fn leading_keyword(&self, node: &SyntaxNode) -> Option<String> {
        node.child_tokens()
            .find(|token| {
                matches!(
                    token.kind(),
                    SyntaxKind::ClassKeyword
                        | SyntaxKind::StructKeyword
                        | SyntaxKind::InterfaceKeyword
                        | SyntaxKind::EnumKeyword
                        | SyntaxKind::DelegateKeyword
                ) || token.contextual_kind() == SyntaxKind::RecordKeyword
            })
            .map(|token| self.tree.text(token.span()))
    }

    /// The type on the left of a member's name.
    fn return_type(&self, node: &SyntaxNode) -> Option<String> {
        let name_start = self
            .identifier(node)
            .or_else(|| {
                node.child_token_of_kind(SyntaxKind::ThisKeyword)
                    .map(|t| t.span())
            })
            .map_or(u32::MAX, TextSpan::start);
        node.children()
            .filter(|child| child.kind().is_type_node())
            // The return type is the type node before the name; a constraint
            // or a base further along is not it.
            .find(|child| child.span().start() < name_start)
            .map(|child| self.tree.text(child.span()))
    }

    fn bases(&self, node: &SyntaxNode) -> Vec<String> {
        let Some(list) = node.child_of_kind(SyntaxKind::BaseList) else {
            return Vec::new();
        };
        list.children()
            .filter(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::SimpleBaseType | SyntaxKind::PrimaryConstructorBaseType
                )
            })
            .filter_map(|base| base.children().next())
            .map(|name| self.tree.text(name.span()))
            .collect()
    }

    fn type_parameters(&self, node: &SyntaxNode) -> Vec<String> {
        let Some(list) = node.child_of_kind(SyntaxKind::TypeParameterList) else {
            return Vec::new();
        };
        list.children()
            .filter(|child| child.kind() == SyntaxKind::TypeParameter)
            .filter_map(|parameter| parameter.child_token_of_kind(SyntaxKind::IdentifierToken))
            .map(|token| self.tree.text(token.span()))
            .collect()
    }

    fn parameters(&self, node: &SyntaxNode) -> Vec<Parameter> {
        let list = node
            .child_of_kind(SyntaxKind::ParameterList)
            .or_else(|| node.child_of_kind(SyntaxKind::BracketedParameterList));
        let Some(list) = list else {
            return Vec::new();
        };
        list.children()
            .filter(|child| child.kind() == SyntaxKind::Parameter)
            .map(|parameter| self.parameter(&parameter))
            .collect()
    }

    fn parameter(&self, node: &SyntaxNode) -> Parameter {
        let passed_by = node
            .child_tokens()
            .find_map(|token| match token.kind() {
                SyntaxKind::ThisKeyword => Some(PassedBy::This),
                SyntaxKind::RefKeyword => Some(PassedBy::Ref),
                SyntaxKind::OutKeyword => Some(PassedBy::Out),
                SyntaxKind::InKeyword => Some(PassedBy::In),
                SyntaxKind::ParamsKeyword => Some(PassedBy::Params),
                _ => None,
            })
            .unwrap_or_default();
        let type_text = node
            .children()
            .find(|child| child.kind().is_type_node())
            .map(|child| self.tree.text(child.span()))
            .unwrap_or_default();
        let name = node
            .child_token_of_kind(SyntaxKind::IdentifierToken)
            .map(|token| self.tree.text(token.span()))
            .unwrap_or_default();
        Parameter {
            name,
            type_text,
            passed_by,
            optional: node.child_of_kind(SyntaxKind::EqualsValueClause).is_some()
                || passed_by == PassedBy::Params,
        }
    }

    fn attributes(&self, node: &SyntaxNode) -> Vec<String> {
        node.children()
            .filter(|child| child.kind() == SyntaxKind::AttributeList)
            .flat_map(|list| list.children())
            .filter(|child| child.kind() == SyntaxKind::Attribute)
            .filter_map(|attribute| attribute.children().next())
            .map(|name| {
                let text = self.tree.text(name.span());
                // `[SerializeField]` and `[SerializeFieldAttribute]` are the
                // same attribute; the short form is what people write and
                // what a rule above should match on.
                let short = text.rsplit('.').next().unwrap_or(&text);
                short
                    .strip_suffix("Attribute")
                    .filter(|stripped| !stripped.is_empty())
                    .unwrap_or(short)
                    .to_owned()
            })
            .collect()
    }

    fn has(&self, node: &SyntaxNode, kind: SyntaxKind) -> bool {
        node.child_token_of_kind(kind).is_some()
    }

    fn has_contextual(&self, node: &SyntaxNode, kind: SyntaxKind) -> bool {
        node.child_tokens()
            .any(|token| token.contextual_kind() == kind)
    }

    fn name_node(&self, node: &SyntaxNode) -> Option<TextSpan> {
        node.children()
            .find(|child| child.kind().is_type_node())
            .map(|child| child.span())
            .or_else(|| self.identifier(node))
    }

    fn qualified_name_of(&self, node: &SyntaxNode) -> String {
        self.name_node(node)
            .map(|span| self.tree.text(span))
            .unwrap_or_default()
    }
}

const fn is_type_declaration(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::ClassDeclaration
            | SyntaxKind::StructDeclaration
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::EnumDeclaration
            | SyntaxKind::RecordDeclaration
            | SyntaxKind::RecordStructDeclaration
            | SyntaxKind::DelegateDeclaration
    )
}

const fn type_kind(kind: SyntaxKind) -> DeclarationKind {
    match kind {
        SyntaxKind::StructDeclaration => DeclarationKind::Struct,
        SyntaxKind::InterfaceDeclaration => DeclarationKind::Interface,
        SyntaxKind::EnumDeclaration => DeclarationKind::Enum,
        SyntaxKind::RecordDeclaration | SyntaxKind::RecordStructDeclaration => {
            DeclarationKind::Record
        }
        SyntaxKind::DelegateDeclaration => DeclarationKind::Delegate,
        _ => DeclarationKind::Class,
    }
}

fn join(container: Option<&str>, name: &str) -> String {
    match container {
        Some(container) if !container.is_empty() => format!("{container}.{name}"),
        _ => name.to_owned(),
    }
}

/// The fields nearly every declaration leaves empty.
fn blank() -> Declaration {
    Declaration {
        name: String::new(),
        kind: DeclarationKind::Class,
        keyword: String::new(),
        name_span: TextSpan::new(0, 0),
        full_span: TextSpan::new(0, 0),
        line: 0,
        depth: 0,
        container: None,
        type_text: None,
        bases: Vec::new(),
        type_parameters: Vec::new(),
        parameters: Vec::new(),
        attributes: Vec::new(),
        is_static: false,
        is_abstract: false,
        is_override: false,
        is_partial: false,
    }
}

// MARK: - keeping it between runs

impl Cacheable for FileOutline {
    const VERSION: u32 = 1;

    fn encode(&self, writer: &mut Writer) {
        writer.u32(self.parse_errors);
        writer.seq(&self.namespaces, |w, name| w.str(name));
        writer.seq(&self.usings, |w, using| {
            w.str(&using.name);
            w.str(using.alias.as_deref().unwrap_or(""));
            w.u8(u8::from(using.is_static) | (u8::from(using.is_global) << 1));
        });
        writer.seq(&self.declarations, |w, declaration| {
            w.str(&declaration.name);
            w.u8(declaration.kind as u8);
            w.str(&declaration.keyword);
            w.u32(declaration.name_span.start());
            w.u32(declaration.name_span.length());
            w.u32(declaration.full_span.start());
            w.u32(declaration.full_span.length());
            w.u32(declaration.line);
            w.u32(declaration.depth);
            w.str(declaration.container.as_deref().unwrap_or(""));
            w.str(declaration.type_text.as_deref().unwrap_or(""));
            w.seq(&declaration.bases, |w, base| w.str(base));
            w.seq(&declaration.type_parameters, |w, name| w.str(name));
            w.seq(&declaration.parameters, |w, parameter| {
                w.str(&parameter.name);
                w.str(&parameter.type_text);
                w.u8(parameter.passed_by as u8);
                w.u8(u8::from(parameter.optional));
            });
            w.seq(&declaration.attributes, |w, name| w.str(name));
            w.u8(u8::from(declaration.is_static)
                | (u8::from(declaration.is_abstract) << 1)
                | (u8::from(declaration.is_override) << 2)
                | (u8::from(declaration.is_partial) << 3));
        });
    }

    fn decode(reader: &mut Reader<'_>) -> Option<Self> {
        let parse_errors = reader.u32()?;
        let namespaces = reader.seq(Reader::string)?;
        let usings = reader.seq(|r| {
            let name = r.string()?;
            let alias = r.string()?;
            let flags = r.u8()?;
            Some(Using {
                name,
                alias: (!alias.is_empty()).then_some(alias),
                is_static: flags & 1 != 0,
                is_global: flags & 2 != 0,
            })
        })?;
        let declarations = reader.seq(|r| {
            let name = r.string()?;
            let kind = DeclarationKind::from_byte(r.u8()?)?;
            let keyword = r.string()?;
            let name_span = TextSpan::new(r.u32()?, r.u32()?);
            let full_span = TextSpan::new(r.u32()?, r.u32()?);
            let line = r.u32()?;
            let depth = r.u32()?;
            let container = r.string()?;
            let type_text = r.string()?;
            let bases = r.seq(Reader::string)?;
            let type_parameters = r.seq(Reader::string)?;
            let parameters = r.seq(|r| {
                let name = r.string()?;
                let type_text = r.string()?;
                let passed_by = match r.u8()? {
                    0 => PassedBy::Value,
                    1 => PassedBy::Ref,
                    2 => PassedBy::Out,
                    3 => PassedBy::In,
                    4 => PassedBy::This,
                    5 => PassedBy::Params,
                    _ => return None,
                };
                Some(Parameter {
                    name,
                    type_text,
                    passed_by,
                    optional: r.u8()? != 0,
                })
            })?;
            let attributes = r.seq(Reader::string)?;
            let flags = r.u8()?;
            Some(Declaration {
                name,
                kind,
                keyword,
                name_span,
                full_span,
                line,
                depth,
                container: (!container.is_empty()).then_some(container),
                type_text: (!type_text.is_empty()).then_some(type_text),
                bases,
                type_parameters,
                parameters,
                attributes,
                is_static: flags & 1 != 0,
                is_abstract: flags & 2 != 0,
                is_override: flags & 4 != 0,
                is_partial: flags & 8 != 0,
            })
        })?;
        Some(Self {
            declarations,
            namespaces,
            usings,
            parse_errors,
        })
    }

    fn weight(&self) -> usize {
        // A rough count: the strings dominate, and the struct around each
        // declaration is about as big again.
        self.declarations
            .iter()
            .map(|declaration| {
                declaration.name.len()
                    + declaration.container.as_ref().map_or(0, String::len)
                    + declaration
                        .parameters
                        .iter()
                        .map(|parameter| parameter.name.len() + parameter.type_text.len() + 32)
                        .sum::<usize>()
                    + 200
            })
            .sum::<usize>()
            + self
                .usings
                .iter()
                .map(|using| using.name.len() + 48)
                .sum::<usize>()
            + 128
    }
}

/// A convenience for callers that only have text.
#[must_use]
pub fn outline(text: &str) -> Arc<FileOutline> {
    Arc::new(FileOutline::of(
        &SourceText::new("Program.cs", text),
        &ParseOptions::default(),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn build(text: &str) -> FileOutline {
        FileOutline::of(
            &SourceText::new("Program.cs", text),
            &ParseOptions::default(),
        )
    }

    fn named<'a>(outline: &'a FileOutline, name: &str) -> &'a Declaration {
        outline
            .declarations
            .iter()
            .find(|declaration| declaration.name == name)
            .unwrap_or_else(|| panic!("no declaration named {name}: {:#?}", outline.declarations))
    }

    #[test]
    fn a_class_brings_its_bases_and_type_parameters() {
        let outline = build("public sealed class Stash<T> : Base, IFoo where T : class { }");
        let stash = named(&outline, "Stash");
        assert_eq!(stash.kind, DeclarationKind::Class);
        assert_eq!(stash.keyword, "class");
        assert_eq!(stash.bases, ["Base", "IFoo"]);
        assert_eq!(stash.type_parameters, ["T"]);
    }

    #[test]
    fn every_flavour_of_type_is_told_apart() {
        let outline = build(
            "class C {} struct S {} interface I {} enum E { A } record R(int X); delegate void D();",
        );
        for (name, kind) in [
            ("C", DeclarationKind::Class),
            ("S", DeclarationKind::Struct),
            ("I", DeclarationKind::Interface),
            ("E", DeclarationKind::Enum),
            ("R", DeclarationKind::Record),
            ("D", DeclarationKind::Delegate),
        ] {
            assert_eq!(named(&outline, name).kind, kind, "{name}");
        }
    }

    #[test]
    fn a_method_brings_its_return_type_and_parameters() {
        let outline = build("class C { public Vector3 Move(int n, string why = \"x\") { } }");
        let move_ = named(&outline, "Move");
        assert_eq!(move_.kind, DeclarationKind::Method);
        assert_eq!(move_.type_text.as_deref(), Some("Vector3"));
        assert_eq!(move_.parameters.len(), 2);
        assert_eq!(move_.parameters[0].type_text, "int");
        assert_eq!(move_.parameters[0].name, "n");
        assert!(!move_.parameters[0].optional);
        assert_eq!(move_.parameters[1].type_text, "string");
        assert!(move_.parameters[1].optional, "a default makes it optional");
    }

    #[test]
    fn an_extension_method_is_recognised_by_its_first_parameter() {
        let outline = build("static class E { public static void Say(this Player p, int n) { } }");
        let say = named(&outline, "Say");
        assert!(say.is_extension_method());
        assert_eq!(say.parameters[0].passed_by, PassedBy::This);
        assert_eq!(say.parameters[0].type_text, "Player");
    }

    #[test]
    fn ref_out_and_in_are_told_apart() {
        let outline =
            build("class C { void M(ref int a, out int b, in int c, params int[] d) { } }");
        let m = named(&outline, "M");
        let kinds: Vec<_> = m.parameters.iter().map(|p| p.passed_by).collect();
        assert_eq!(
            kinds,
            [PassedBy::Ref, PassedBy::Out, PassedBy::In, PassedBy::Params]
        );
    }

    #[test]
    fn one_field_declaration_of_several_names_declares_several_fields() {
        let outline = build("class C { private int a, b, c; }");
        for name in ["a", "b", "c"] {
            let field = named(&outline, name);
            assert_eq!(field.kind, DeclarationKind::Field);
            assert_eq!(field.type_text.as_deref(), Some("int"));
        }
    }

    #[test]
    fn attributes_come_through_without_their_suffix() {
        let outline = build(
            "class C { [SerializeField] private float _speed; [UnityEngine.RangeAttribute(0,1)] int _n; }",
        );
        assert_eq!(named(&outline, "_speed").attributes, ["SerializeField"]);
        assert_eq!(named(&outline, "_n").attributes, ["Range"]);
    }

    #[test]
    fn usings_bring_their_aliases_and_kind() {
        let outline = build(
            "using System;\nusing static System.Math;\nusing Vec = UnityEngine.Vector3;\nglobal using System.Linq;\n",
        );
        assert_eq!(outline.usings.len(), 4);
        assert_eq!(outline.usings[0].name, "System");
        assert!(outline.usings[1].is_static);
        assert_eq!(outline.usings[2].alias.as_deref(), Some("Vec"));
        assert_eq!(outline.usings[2].name, "UnityEngine.Vector3");
        assert!(outline.usings[3].is_global);
    }

    #[test]
    fn nested_namespaces_qualify_what_is_inside_them() {
        let outline = build("namespace A { namespace B { class C { void M() {} } } }");
        assert_eq!(named(&outline, "C").container.as_deref(), Some("A.B"));
        assert_eq!(named(&outline, "M").container.as_deref(), Some("A.B.C"));
        assert_eq!(named(&outline, "C").qualified_name(), "A.B.C");
        assert!(outline.namespaces.contains(&"A.B".to_owned()));
    }

    #[test]
    fn a_file_scoped_namespace_qualifies_just_the_same() {
        let outline = build("namespace Game.Systems;\nclass Pawn { }");
        assert_eq!(
            named(&outline, "Pawn").qualified_name(),
            "Game.Systems.Pawn"
        );
    }

    #[test]
    fn a_nested_type_is_qualified_by_the_type_around_it() {
        let outline = build("namespace N { class Outer { class Inner { } } }");
        assert_eq!(named(&outline, "Inner").qualified_name(), "N.Outer.Inner");
    }

    #[test]
    fn properties_indexers_events_and_enum_members_all_appear() {
        let outline = build(
            "class C { public int P { get; set; } public int this[int i] => i; public event Action Died; }\nenum E { A, B = 2 }",
        );
        assert_eq!(named(&outline, "P").kind, DeclarationKind::Property);
        assert_eq!(named(&outline, "this[]").kind, DeclarationKind::Indexer);
        assert_eq!(named(&outline, "Died").kind, DeclarationKind::Event);
        assert_eq!(named(&outline, "A").kind, DeclarationKind::EnumMember);
        assert_eq!(named(&outline, "B").kind, DeclarationKind::EnumMember);
    }

    #[test]
    fn a_constructor_is_not_a_method_and_keeps_its_parameters() {
        // The class and the constructor share a name, which is why the kind
        // has to carry the difference rather than the name.
        let outline = build("class Pawn { public Pawn(int hp) { } }");
        let ctor = outline
            .declarations
            .iter()
            .find(|declaration| declaration.kind == DeclarationKind::Constructor)
            .expect("a constructor");
        assert_eq!(ctor.name, "Pawn");
        assert_eq!(ctor.parameters.len(), 1);
        assert_eq!(ctor.parameters[0].type_text, "int");
        assert_eq!(ctor.container.as_deref(), Some("Pawn"));
    }

    #[test]
    fn modifiers_are_recorded() {
        let outline = build(
            "abstract partial class C { public static void S() {} public override void O() {} }",
        );
        let c = named(&outline, "C");
        assert!(c.is_abstract);
        assert!(c.is_partial);
        assert!(named(&outline, "S").is_static);
        assert!(named(&outline, "O").is_override);
    }

    // MARK: - the things a shape-matching outline gets wrong

    #[test]
    fn a_call_is_not_a_method_declaration() {
        // `Foo(x)` on its own line has the shape `Name(...)`, and a heuristic
        // reading of it declares a method. The grammar knows better.
        let outline =
            build("class C { void M() { Helper(1); var v = Other(2); if (Test(3)) { } } }");
        let names: Vec<&str> = outline
            .declarations
            .iter()
            .map(|declaration| declaration.name.as_str())
            .collect();
        assert_eq!(
            names,
            ["C", "M"],
            "only the class and the method: {names:?}"
        );
    }

    #[test]
    fn a_local_variable_is_not_a_field() {
        let outline = build("class C { void M() { int local = 1; Vector3 position = default; } }");
        assert!(
            !outline
                .declarations
                .iter()
                .any(|d| d.name == "local" || d.name == "position"),
            "locals are not declarations of the file: {:#?}",
            outline.declarations,
        );
    }

    #[test]
    fn an_expression_bodied_member_is_not_mistaken_for_something_else() {
        let outline = build("class C { public int N => 1 + 2; public int M() => 3; }");
        assert_eq!(named(&outline, "N").kind, DeclarationKind::Property);
        assert_eq!(named(&outline, "M").kind, DeclarationKind::Method);
    }

    #[test]
    fn a_linq_query_declares_nothing() {
        let outline = build(
            "class C { void M() { var q = from x in xs where x > 1 select new { A = x }; } }",
        );
        let names: Vec<&str> = outline
            .declarations
            .iter()
            .map(|declaration| declaration.name.as_str())
            .collect();
        assert_eq!(names, ["C", "M"], "{names:?}");
    }

    #[test]
    fn a_generic_call_is_not_a_declaration() {
        // `Stash<Health>.Get()` has angle brackets and parentheses, which is
        // exactly the shape a heuristic reads as a generic method declaration.
        let outline = build("class C { void M() { var h = Stash<Health>.Get(); } }");
        let names: Vec<&str> = outline
            .declarations
            .iter()
            .map(|declaration| declaration.name.as_str())
            .collect();
        assert_eq!(names, ["C", "M"], "{names:?}");
    }

    #[test]
    fn a_local_function_is_not_a_member_of_the_type() {
        let outline = build("class C { void M() { int Helper(int n) => n; Helper(1); } }");
        assert!(
            !outline.declarations.iter().any(|d| d.name == "Helper"),
            "a local function belongs to its method: {:#?}",
            outline.declarations,
        );
    }

    #[test]
    fn a_declaration_inside_a_dead_branch_is_left_out() {
        let outline = build("#if NEVER\nclass Gone { }\n#endif\nclass Here { }\n");
        assert!(outline.declarations.iter().any(|d| d.name == "Here"));
        assert!(
            !outline.declarations.iter().any(|d| d.name == "Gone"),
            "code the preprocessor removed is not in the file",
        );
    }

    #[test]
    fn a_declaration_inside_a_live_branch_is_kept() {
        let outline = FileOutline::of(
            &SourceText::new("A.cs", "#if DEBUG\nclass Present { }\n#endif\n"),
            &ParseOptions::with_symbols(["DEBUG"]),
        );
        assert!(outline.declarations.iter().any(|d| d.name == "Present"));
    }

    // MARK: - what is around the cursor

    #[test]
    fn the_declarations_around_an_offset_come_innermost_first() {
        let text = "namespace N { class C { void M() { /*HERE*/ } } }";
        let outline = build(text);
        let offset = text.find("/*HERE*/").expect("a marker") as u32;
        let names: Vec<&str> = outline
            .enclosing(offset)
            .iter()
            .map(|declaration| declaration.name.as_str())
            .collect();
        assert_eq!(names, ["M", "C", "N"]);
    }

    // MARK: - surviving to the next run

    #[test]
    fn an_outline_survives_being_written_and_read_back() {
        let outline = build(
            "using System;\nusing Vec = UnityEngine.Vector3;\nnamespace Game;\n\
             [Serializable] public sealed partial class Pawn<T> : Base, IFoo {\n\
                 [SerializeField] private float _speed = 1f;\n\
                 public int Health { get; private set; }\n\
                 public override void Damage(ref int n, string why = \"x\") { }\n\
                 public static void Say(this Pawn<T> p) { }\n\
                 public int this[int i] => i;\n\
                 enum Mode { A, B = 2 }\n\
             }\n",
        );
        let mut writer = Writer::new();
        outline.encode(&mut writer);
        let bytes = writer.finish();
        let read = FileOutline::decode(&mut Reader::new(&bytes)).expect("it should read back");
        assert_eq!(read, outline);
    }

    #[test]
    fn a_truncated_outline_file_reads_as_nothing_rather_than_as_rubbish() {
        let outline = build("class C { void M(int a) {} }");
        let mut writer = Writer::new();
        outline.encode(&mut writer);
        let bytes = writer.finish();
        for length in 0..bytes.len() {
            let read = FileOutline::decode(&mut Reader::new(&bytes[..length]));
            assert!(read.is_none() || read.as_ref() != Some(&outline));
        }
    }

    #[test]
    fn an_empty_file_outlines_to_nothing() {
        let outline = build("");
        assert!(outline.declarations.is_empty());
        assert!(outline.usings.is_empty());
    }

    #[test]
    fn a_file_that_does_not_parse_still_gives_what_it_can() {
        // The parser recovers rather than failing, so a file being typed into
        // still has an outline — which is the whole point of having one.
        let outline = build("class C { void M( { int x = }");
        assert!(outline.parse_errors > 0, "the errors should be counted");
        assert!(
            outline.declarations.iter().any(|d| d.name == "C"),
            "the class is still there: {:#?}",
            outline.declarations,
        );
    }
}
