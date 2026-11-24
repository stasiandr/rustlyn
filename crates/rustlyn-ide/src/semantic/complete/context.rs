//! Where the cursor is, in the terms completion decides by.
//!
//! Roslyn answers "what can go here?" from the token in front of the word
//! being typed — its *target token* — and not from the node the word ended
//! up in, because the word is half written and the parser has made the best
//! of it: `int co` is a declaration of `co`, `override To` is a field of
//! type `To`, and neither says what the person is about to write. The token
//! before the word was there before they started typing it, and the grammar
//! around it is settled. Everything here reads that token and its parent.

use rustlyn_syntax::{SyntaxKind as K, SyntaxNode, SyntaxToken};

/// The word being completed and what is in front of it.
pub(super) struct Site {
    /// Where the word being typed starts.
    pub start: u32,
    /// What has been typed of it.
    pub word: String,
    /// The last real token before the word: what decides the context.
    pub target: Option<SyntaxToken>,
}

impl Site {
    pub(super) fn new(root: &SyntaxNode, text: &str, offset: u32) -> Self {
        let bytes = text.as_bytes();
        let offset = offset.min(bytes.len() as u32);
        let mut start = offset as usize;
        while start > 0
            && (bytes[start - 1].is_ascii_alphanumeric()
                || bytes[start - 1] == b'_'
                || bytes[start - 1] >= 0x80)
        {
            start -= 1;
        }
        let word = text[start..offset as usize].to_string();
        let start = start as u32;
        Self {
            start,
            word,
            target: token_before(root, start),
        }
    }
}

/// The last token with text that ends at or before `offset`: missing tokens
/// the parser made up, and trivia, are stepped over.
pub(super) fn token_before(root: &SyntaxNode, offset: u32) -> Option<SyntaxToken> {
    let mut position = offset;
    loop {
        let token = root.find_token(position.checked_sub(1)?)?;
        if !token.span().is_empty() && token.span().end() <= offset {
            return Some(token);
        }
        let back = token.full_span().start();
        if back >= position {
            position -= 1;
        } else {
            position = back;
        }
        if position == 0 {
            return None;
        }
    }
}

/// The real token in front of `token`.
pub(super) fn previous_token(root: &SyntaxNode, token: &SyntaxToken) -> Option<SyntaxToken> {
    token_before(root, token.span().start())
}

/// What kind of place the cursor is in. The first matching answer wins:
/// a comment is nothing at all, a `.` is a member, and so on down to plain
/// code, which is described by [`Code`].
pub(super) enum Spot {
    /// A comment, a string, text a directive disabled: nothing is offered.
    Nothing,
    /// Inside a `///` comment.
    Documentation,
    /// On a `#` line.
    Directive,
    /// After `.`, `?.` or `::`.
    Member(SyntaxToken),
    /// After `using`, `using static` or `using Alias =`.
    Using { is_static: bool, alias: bool },
    /// After `using A.B.`: the dotted name so far, and whether types can
    /// follow (`using static`, `using X =`).
    UsingMember { path: String, with_types: bool },
    /// Where an attribute's name goes: `[|`, `[A, |`.
    Attribute,
    /// After `override` in a type: the start of the modifiers typed so far.
    Override { first: SyntaxToken },
    /// After `partial` in a type, where a method goes.
    Partial { first: SyntaxToken },
    /// Where a member of the object being created is assigned:
    /// `new C { | }`.
    Initializer(SyntaxNode),
    /// Where a new name is being written, after its type: `int |`. The
    /// node is the type; whether it is one is for the binder to say.
    Name { ty: SyntaxNode, of: NameOf },
    /// Anywhere else.
    Code(Code),
}

/// What a name being declared will be, which decides how it is spelled.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum NameOf {
    Local,
    Parameter,
    /// A field or property: whether it is public decides its case.
    Member {
        public: bool,
    },
}

/// Code: which of the grammar's broad positions the cursor is at. More than
/// one can hold — a statement can start with an expression, and top-level
/// code is both where statements and types go.
#[derive(Default, Debug)]
pub(super) struct Code {
    /// A statement can start here.
    pub statement: bool,
    /// Code outside any type: top-level statements.
    pub global: bool,
    /// An expression can start here.
    pub expression: bool,
    /// Only a type can be written here.
    pub type_only: bool,
    /// Where `var` is also a type: a local's declaration.
    pub allows_var: bool,
    /// Where `void` is also a type: a return type.
    pub allows_void: bool,
    /// A member of a type can be declared here.
    pub member: bool,
    /// A type or namespace can be declared here.
    pub type_declaration: bool,
    /// The modifiers already written in front of the cursor.
    pub modifiers: Vec<String>,
    /// Right after an expression, where only an operator can follow.
    pub after_expression: bool,
    /// After `where T :`.
    pub constraint: bool,
    /// Inside a property's or event's `{ }`, where accessors go.
    pub accessors: Option<SyntaxNode>,
    /// After `foreach (var x`.
    pub foreach_in: bool,
    /// After a generic declaration's header, where `where` goes.
    pub where_clause: bool,
    /// Right inside a `switch`'s braces, where only a label goes.
    pub switch_labels: bool,
    /// Where a parameter starts: its modifiers go here.
    pub parameter: bool,
    /// An argument of a call: `ref`, `out` and `in` go here.
    pub argument: bool,
    /// After `is` or `case`: a pattern.
    pub pattern: bool,
    /// After `new`.
    pub after_new: bool,
    /// In a type's base list, where only classes and interfaces go.
    pub base_list: bool,
}

const MODIFIERS: &[&str] = &[
    "public",
    "private",
    "protected",
    "internal",
    "static",
    "abstract",
    "sealed",
    "virtual",
    "override",
    "readonly",
    "const",
    "extern",
    "unsafe",
    "volatile",
    "new",
    "partial",
    "async",
    "required",
    "file",
];

pub(super) fn is_modifier(text: &str) -> bool {
    MODIFIERS.contains(&text)
}

/// Whether a node declares a type whose body holds members.
pub(super) const fn is_type_declaration(kind: K) -> bool {
    matches!(
        kind,
        K::ClassDeclaration
            | K::StructDeclaration
            | K::InterfaceDeclaration
            | K::RecordDeclaration
            | K::RecordStructDeclaration
    )
}

/// Whether a node is a member of a type, the kind a modifier starts.
const fn is_member_declaration(kind: K) -> bool {
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
            | K::IncompleteMember
            | K::DelegateDeclaration
            | K::EnumDeclaration
    ) || is_type_declaration(kind)
}

/// Whether a block ending in `}` ends a statement, so another can follow.
const fn block_is_statement(parent: K) -> bool {
    matches!(
        parent,
        K::Block
            | K::IfStatement
            | K::ElseClause
            | K::WhileStatement
            | K::ForStatement
            | K::ForEachStatement
            | K::ForEachVariableStatement
            | K::UsingStatement
            | K::LockStatement
            | K::FixedStatement
            | K::CheckedStatement
            | K::UncheckedStatement
            | K::UnsafeStatement
            | K::TryStatement
            | K::CatchClause
            | K::FinallyClause
            | K::LocalFunctionStatement
            | K::SwitchSection
            | K::LabeledStatement
            | K::GlobalStatement
    )
}

/// The innermost declaration that holds `node`: a type, a namespace, or the
/// file.
pub(super) fn container_of(node: &SyntaxNode) -> Option<SyntaxNode> {
    std::iter::once(node.clone())
        .chain(node.ancestors())
        .find(|ancestor| {
            is_type_declaration(ancestor.kind())
                || matches!(
                    ancestor.kind(),
                    K::NamespaceDeclaration
                        | K::FileScopedNamespaceDeclaration
                        | K::CompilationUnit
                        | K::Block
                        | K::ArrowExpressionClause
                        | K::EqualsValueClause
                        | K::AccessorList
                )
        })
}

/// Whether a file's top level can hold statements: it declares no
/// namespace to put them in.
fn allows_top_level_statements(root: &SyntaxNode) -> bool {
    !root.children().any(|child| {
        matches!(
            child.kind(),
            K::FileScopedNamespaceDeclaration | K::NamespaceDeclaration
        )
    })
}

/// What kind of place `site` is in.
pub(super) fn classify(root: &SyntaxNode, site: &Site) -> Spot {
    if let Some(spot) = in_trivia(root, site.start) {
        return spot;
    }
    let Some(target) = site.target.clone() else {
        // The start of the file.
        return Spot::Code(Code {
            type_declaration: true,
            statement: allows_top_level_statements(root),
            global: allows_top_level_statements(root),
            expression: allows_top_level_statements(root),
            ..Code::default()
        });
    };
    if site.word.starts_with(|c: char| c.is_ascii_digit()) {
        // A number being typed.
        return Spot::Nothing;
    }
    // `x.‸.Name`: the name of a member deleted from between two dots, which
    // the lexer reads as one `..`. What is wanted is still a member of `x`.
    if site.word.is_empty()
        && let Some(dots) = root.find_token(site.start.saturating_sub(1))
        && dots.kind() == K::DotDotToken
        && dots.span().start() + 1 == site.start
        && dots.parent().kind() == K::RangeExpression
        && dots
            .parent()
            .children()
            .next()
            .is_some_and(|left| left.span().end() == dots.span().start())
    {
        return Spot::Member(dots);
    }
    if target.kind() == K::DotToken
        && let Some(spot) = using_line(root, site, &target)
    {
        return spot;
    }
    if matches!(target.kind(), K::DotToken | K::ColonColonToken) {
        if target.kind() == K::DotToken && target.parent().kind() == K::NumericLiteralExpression {
            return Spot::Nothing;
        }
        return Spot::Member(target);
    }
    if target.kind() == K::MinusGreaterThanToken {
        return Spot::Nothing;
    }
    let parent = target.parent().clone();

    // `using`, `using static`, `using A =`.
    if parent.kind() == K::UsingDirective {
        match target.kind() {
            K::UsingKeyword => {
                return Spot::Using {
                    is_static: false,
                    alias: false,
                };
            }
            K::StaticKeyword => {
                return Spot::Using {
                    is_static: true,
                    alias: false,
                };
            }
            _ => {}
        }
    }
    if parent.kind() == K::NameEquals
        && target.kind() == K::EqualsToken
        && parent
            .parent()
            .is_some_and(|using| using.kind() == K::UsingDirective)
    {
        return Spot::Using {
            is_static: false,
            alias: true,
        };
    }

    // `[|` and `[A, |` before a declaration.
    if (matches!(target.kind(), K::OpenBracketToken | K::CommaToken)
        && parent.kind() == K::AttributeList)
        || (target.kind() == K::ColonToken && parent.kind() == K::AttributeTargetSpecifier)
    {
        return Spot::Attribute;
    }

    // `new C { | }`
    if matches!(target.kind(), K::OpenBraceToken | K::CommaToken)
        && let Some(initializer) = member_initializer(&parent, site.start)
    {
        return Spot::Initializer(initializer);
    }

    // Modifiers in front of a member: `public override |`.
    if is_modifier(target.text())
        && let Some(spot) = after_modifiers(root, &target)
    {
        return spot;
    }

    // A new name after its type: `int |`, `List<int> |`.
    if let Some(spot) = declaration_name(&target) {
        return spot;
    }

    Spot::Code(code_at(root, &target))
}

/// `using A.B.|` on a line of its own, outside any code. Read from the text:
/// a half-written `using` is not always parsed as one.
fn using_line(root: &SyntaxNode, site: &Site, dot: &SyntaxToken) -> Option<Spot> {
    let in_code = dot
        .parent()
        .ancestors()
        .any(|node| node.kind() == K::Block || is_type_declaration(node.kind()));
    if in_code {
        return None;
    }
    let text = root.full_text();
    let before = &text[..site.start as usize];
    let line = before.rsplit('\n').next().unwrap_or(before).trim_start();
    let line = line.strip_prefix("global").map_or(line, str::trim_start);
    let rest = line.strip_prefix("using")?;
    if !rest.starts_with(char::is_whitespace) {
        return None;
    }
    let mut rest = rest.trim_start();
    let mut with_types = false;
    if let Some(after) = rest.strip_prefix("static")
        && after.starts_with(char::is_whitespace)
    {
        rest = after.trim_start();
        with_types = true;
    }
    if let Some((alias, target)) = rest.split_once('=') {
        if !alias
            .trim()
            .chars()
            .all(|c| c.is_alphanumeric() || c == '_')
        {
            return None;
        }
        rest = target.trim_start();
        with_types = true;
    }
    let path = rest.strip_suffix('.')?;
    let plain = path
        .chars()
        .all(|c| c.is_alphanumeric() || c == '_' || c == '.' || c == ':');
    plain.then(|| Spot::UsingMember {
        path: path.to_string(),
        with_types,
    })
}

/// Whether `offset` is in a comment, a directive or disabled text, and which.
pub(super) fn in_trivia(root: &SyntaxNode, offset: u32) -> Option<Spot> {
    let mut candidates = Vec::new();
    if let Some(token) = root.find_token(offset) {
        candidates.extend(token.leading_trivia());
        candidates.extend(token.trailing_trivia());
        if token.span().start() < offset && offset < token.span().end() {
            // In the middle of a token: a string's or a character's text.
            if token.kind().is_literal_token()
                || matches!(
                    token.kind(),
                    K::InterpolatedStringTextToken | K::InterpolatedStringStartToken
                )
            {
                return Some(Spot::Nothing);
            }
        }
    }
    if let Some(token) = offset
        .checked_sub(1)
        .and_then(|before| root.find_token(before))
    {
        candidates.extend(token.leading_trivia());
        candidates.extend(token.trailing_trivia());
        if token.span().start() < offset
            && offset <= token.span().end()
            && is_unterminated_text(&token, offset)
        {
            return Some(Spot::Nothing);
        }
    }
    for trivia in candidates {
        let span = trivia.span();
        if !(span.start() < offset && offset <= span.end()) {
            continue;
        }
        let kind = trivia.kind();
        let name = format!("{kind:?}");
        return Some(match kind {
            K::SingleLineDocumentationCommentTrivia | K::MultiLineDocumentationCommentTrivia => {
                Spot::Documentation
            }
            K::SingleLineCommentTrivia | K::MultiLineCommentTrivia | K::DisabledTextTrivia => {
                // A `#` line in disabled text is still a directive.
                if kind == K::DisabledTextTrivia && on_directive_line(root, offset) {
                    Spot::Directive
                } else {
                    Spot::Nothing
                }
            }
            K::WhitespaceTrivia | K::EndOfLineTrivia => continue,
            _ if name.ends_with("DirectiveTrivia") => Spot::Directive,
            _ => continue,
        });
    }
    // A `#` typed at the end of the file or before a token the parser has
    // not reattached yet.
    if on_directive_line(root, offset) {
        return Some(Spot::Directive);
    }
    None
}

/// Whether a literal token runs up to `offset` without being closed: typing
/// at the end of `"abc` is typing inside the string.
fn is_unterminated_text(token: &SyntaxToken, offset: u32) -> bool {
    if offset < token.span().end() {
        return token.kind().is_literal_token() || token.kind() == K::InterpolatedStringTextToken;
    }
    let text = token.text();
    match token.kind() {
        K::StringLiteralToken => {
            text.len() < 2 || !text.ends_with('"') || text == "@\"" || text.ends_with("\\\"")
        }
        K::CharacterLiteralToken => text.len() < 2 || !text.ends_with('\''),
        K::InterpolatedStringTextToken => true,
        _ => false,
    }
}

/// Whether the line `offset` is on starts with `#` before it.
fn on_directive_line(root: &SyntaxNode, offset: u32) -> bool {
    let text = root.full_text();
    let before = &text[..(offset as usize).min(text.len())];
    let line = before.rsplit('\n').next().unwrap_or(before);
    line.trim_start().starts_with('#')
}

/// The object initializer a `{` or `,` belongs to, when it assigns members
/// rather than adding elements.
fn member_initializer(parent: &SyntaxNode, start: u32) -> Option<SyntaxNode> {
    if !matches!(
        parent.kind(),
        K::ObjectInitializerExpression | K::CollectionInitializerExpression
    ) {
        return None;
    }
    let creation = parent.parent()?;
    if !matches!(
        creation.kind(),
        K::ObjectCreationExpression | K::ImplicitObjectCreationExpression
    ) {
        return None;
    }
    // Every element but the one being typed must be an assignment: one
    // plain value makes it a collection initializer.
    let assigns = parent
        .children()
        .filter(|element| !(element.span().start() <= start && start <= element.span().end()))
        .all(|element| element.kind() == K::SimpleAssignmentExpression);
    assigns.then(|| parent.clone())
}

/// The modifiers in front of `last`, back to where the declaration starts,
/// and what they are in front of.
fn after_modifiers(root: &SyntaxNode, last: &SyntaxToken) -> Option<Spot> {
    let mut words = vec![last.clone()];
    let mut before = previous_token(root, last);
    while let Some(token) = before.clone() {
        if !is_modifier(token.text()) {
            break;
        }
        before = previous_token(root, &token);
        words.push(token);
    }
    words.reverse();
    // What comes before the first modifier must end something, or the
    // words are not modifiers: `x = new |` is an expression.
    let starts = before.as_ref().is_none_or(|token| {
        matches!(
            token.kind(),
            K::OpenBraceToken | K::CloseBraceToken | K::SemicolonToken | K::CloseBracketToken
        )
    });
    if !starts {
        return None;
    }
    let first = words.first()?.clone();
    let parent = last.parent().clone();
    // A modifier in front of a local or a local function.
    let in_body = std::iter::once(parent.clone())
        .chain(parent.ancestors())
        .take_while(|node| !is_type_declaration(node.kind()))
        .any(|node| matches!(node.kind(), K::Block | K::GlobalStatement));
    if in_body {
        if words.iter().any(|word| word.text() == "new") {
            return None;
        }
        return Some(Spot::Code(Code {
            type_only: true,
            allows_void: true,
            modifiers: words.iter().map(|word| word.text().to_string()).collect(),
            statement: false,
            ..Code::default()
        }));
    }
    let container = container_of(&parent)?;
    let in_type = is_type_declaration(container.kind())
        && container
            .child_token_of_kind(K::OpenBraceToken)
            .is_some_and(|brace| brace.span().end() <= first.span().start());
    let texts: Vec<String> = words.iter().map(|word| word.text().to_string()).collect();
    if in_type && texts.iter().any(|word| word == "override") {
        return Some(Spot::Override { first });
    }
    if in_type && texts.iter().any(|word| word == "partial") {
        return Some(Spot::Partial { first });
    }
    Some(Spot::Code(Code {
        member: in_type,
        type_declaration: !in_type,
        allows_void: in_type,
        modifiers: texts,
        ..Code::default()
    }))
}

/// `int |`: the cursor is where the name of something declared with that
/// type goes.
fn declaration_name(target: &SyntaxToken) -> Option<Spot> {
    // `(Item |)`: the parser takes a lone word for the parameter's name,
    // but with a space typed after it, it is the type.
    let parent = target.parent();
    if target.kind() == K::IdentifierToken
        && parent.kind() == K::Parameter
        && !parent.children().any(|child| child.kind().is_type_node())
    {
        return Some(Spot::Name {
            ty: parent.clone(),
            of: NameOf::Parameter,
        });
    }
    // The largest type that ends with the target.
    let mut ty: Option<SyntaxNode> = None;
    for node in std::iter::once(target.parent().clone()).chain(target.parent().ancestors()) {
        let is_type = node.kind().is_type_node() && node.kind() != K::TypeArgumentList;
        let ends_here = node
            .last_token_real()
            .is_some_and(|last| last.span() == target.span());
        if is_type && ends_here {
            ty = Some(node);
        } else if node.kind() == K::TypeArgumentList && ends_here {
            continue;
        } else {
            break;
        }
    }
    let ty = ty?;
    let parent = ty.parent()?.clone();
    if ty.text().trim() == "var" && parent.kind() != K::Parameter {
        return None;
    }
    let of = match parent.kind() {
        K::VariableDeclaration => {
            let declaration = parent.parent()?;
            match declaration.kind() {
                K::FieldDeclaration | K::EventFieldDeclaration => NameOf::Member {
                    public: declaration.child_tokens().any(|token| {
                        matches!(token.kind(), K::PublicKeyword | K::ProtectedKeyword)
                            || token.kind() == K::InternalKeyword
                    }),
                },
                _ => NameOf::Local,
            }
        }
        K::Parameter => NameOf::Parameter,
        K::ForEachStatement | K::DeclarationExpression => NameOf::Local,
        K::CatchDeclaration => NameOf::Local,
        K::ExpressionStatement | K::GlobalStatement => {
            // `Foo |` on its own is a declaration only if `Foo` is a type,
            // which the binder decides.
            NameOf::Local
        }
        K::IncompleteMember => NameOf::Member {
            public: parent.child_tokens().any(|token| {
                matches!(
                    token.kind(),
                    K::PublicKeyword | K::ProtectedKeyword | K::InternalKeyword
                )
            }),
        },
        _ => return None,
    };
    // In an expression statement, the type must be all there is.
    if parent.kind() == K::ExpressionStatement
        && !matches!(
            ty.kind(),
            K::PredefinedType
                | K::IdentifierName
                | K::GenericName
                | K::QualifiedName
                | K::ArrayType
                | K::NullableType
        )
    {
        return None;
    }
    Some(Spot::Name { ty, of })
}

/// A trait for a node's last token that is not a missing one.
trait LastReal {
    fn last_token_real(&self) -> Option<SyntaxToken>;
}

impl LastReal for SyntaxNode {
    fn last_token_real(&self) -> Option<SyntaxToken> {
        self.descendant_tokens()
            .filter(|token| !token.is_missing() && !token.span().is_empty())
            .last()
    }
}

/// The broad position of code after `target`.
#[allow(clippy::too_many_lines)] // one grammar, read one token at a time
pub(super) fn code_at(root: &SyntaxNode, target: &SyntaxToken) -> Code {
    let parent = target.parent().clone();
    let grand = parent.parent().cloned();
    let grand_kind = grand.as_ref().map_or(K::None, SyntaxNode::kind);
    let mut code = Code::default();
    let statement = |global: bool| Code {
        statement: true,
        expression: true,
        global,
        type_declaration: global,
        ..Code::default()
    };
    let in_global = |node: &SyntaxNode| {
        std::iter::once(node.clone())
            .chain(node.ancestors())
            .any(|node| node.kind() == K::GlobalStatement)
    };
    // Where a declaration ended: what comes next is decided by where it is.
    let after_declaration = |declaration: &SyntaxNode| -> Code {
        let container = declaration
            .parent()
            .cloned()
            .unwrap_or_else(|| root.clone());
        if is_type_declaration(container.kind()) {
            Code {
                member: true,
                allows_void: true,
                ..Code::default()
            }
        } else if container.kind() == K::CompilationUnit && allows_top_level_statements(root) {
            statement(true)
        } else {
            Code {
                type_declaration: true,
                ..Code::default()
            }
        }
    };

    match target.kind() {
        K::OpenBraceToken => match parent.kind() {
            K::Block => return statement(in_global(&parent)),
            kind if is_type_declaration(kind) => {
                return Code {
                    member: true,
                    allows_void: true,
                    ..Code::default()
                };
            }
            K::NamespaceDeclaration => {
                return Code {
                    type_declaration: true,
                    ..Code::default()
                };
            }
            K::AccessorList => {
                code.accessors = Some(parent);
                return code;
            }
            K::SwitchStatement => {
                code.switch_labels = true;
                return code;
            }
            K::EnumDeclaration => return code,
            _ => {
                code.expression = true;
                return code;
            }
        },
        K::SemicolonToken => {
            if parent.kind() == K::ForStatement {
                code.expression = true;
                return code;
            }
            if parent.kind().is_statement_node() {
                return statement(in_global(&parent));
            }
            match parent.kind() {
                K::UsingDirective | K::ExternAliasDirective | K::FileScopedNamespaceDeclaration => {
                    let at_top = parent
                        .parent()
                        .is_none_or(|container| container.kind() == K::CompilationUnit);
                    let top_level = at_top
                        && parent.kind() != K::FileScopedNamespaceDeclaration
                        && allows_top_level_statements(root);
                    return Code {
                        type_declaration: true,
                        statement: top_level,
                        expression: top_level,
                        global: top_level,
                        ..Code::default()
                    };
                }
                kind if is_member_declaration(kind) => return after_declaration(&parent),
                K::GetAccessorDeclaration
                | K::SetAccessorDeclaration
                | K::InitAccessorDeclaration
                | K::AddAccessorDeclaration
                | K::RemoveAccessorDeclaration
                | K::UnknownAccessorDeclaration => {
                    code.accessors = grand;
                    return code;
                }
                _ => return code,
            }
        }
        K::CloseBraceToken => match parent.kind() {
            K::Block => {
                let owner = grand_kind;
                if block_is_statement(owner) {
                    return statement(in_global(&parent));
                }
                if matches!(
                    owner,
                    K::GetAccessorDeclaration
                        | K::SetAccessorDeclaration
                        | K::InitAccessorDeclaration
                        | K::AddAccessorDeclaration
                        | K::RemoveAccessorDeclaration
                        | K::UnknownAccessorDeclaration
                ) {
                    code.accessors = grand.and_then(|accessor| accessor.parent().cloned());
                    return code;
                }
                if is_member_declaration(owner) {
                    return after_declaration(grand.as_ref().unwrap_or(&parent));
                }
                if matches!(
                    owner,
                    K::ParenthesizedLambdaExpression
                        | K::SimpleLambdaExpression
                        | K::AnonymousMethodExpression
                ) {
                    code.after_expression = true;
                }
                return code;
            }
            K::SwitchStatement => return statement(in_global(&parent)),
            kind if is_member_declaration(kind) => return after_declaration(&parent),
            K::NamespaceDeclaration => {
                return Code {
                    type_declaration: true,
                    ..Code::default()
                };
            }
            K::AccessorList => {
                if let Some(property) = grand {
                    return after_declaration(&property);
                }
                return code;
            }
            kind if kind.is_expression_node() => {
                code.after_expression = true;
                return code;
            }
            _ => return code,
        },
        K::CloseBracketToken if parent.kind() == K::AttributeList => {
            return match grand_kind {
                K::Parameter => Code {
                    type_only: true,
                    parameter: true,
                    ..Code::default()
                },
                K::CompilationUnit => Code {
                    type_declaration: true,
                    ..Code::default()
                },
                kind if is_member_declaration(kind) => {
                    let owner = grand
                        .as_ref()
                        .and_then(|declaration| declaration.parent().cloned());
                    if owner.is_some_and(|owner| is_type_declaration(owner.kind())) {
                        Code {
                            member: true,
                            allows_void: true,
                            ..Code::default()
                        }
                    } else {
                        Code {
                            type_declaration: true,
                            ..Code::default()
                        }
                    }
                }
                _ => code,
            };
        }
        K::CloseParenToken => {
            if matches!(
                parent.kind(),
                K::IfStatement
                    | K::WhileStatement
                    | K::ForStatement
                    | K::ForEachStatement
                    | K::ForEachVariableStatement
                    | K::UsingStatement
                    | K::LockStatement
                    | K::FixedStatement
            ) {
                return statement(false);
            }
            if parent.kind() == K::ParameterList
                && grand.as_ref().is_some_and(|method| {
                    matches!(
                        method.kind(),
                        K::MethodDeclaration | K::LocalFunctionStatement
                    ) && method.child_of_kind(K::TypeParameterList).is_some()
                })
            {
                code.where_clause = true;
                return code;
            }
            if parent.kind() == K::CastExpression {
                code.expression = true;
                return code;
            }
            if parent.kind().is_expression_node() || parent.kind() == K::ArgumentList {
                code.after_expression = true;
            }
            return code;
        }
        K::ElseKeyword | K::DoKeyword => return statement(false),
        K::ColonToken
            if matches!(
                parent.kind(),
                K::LabeledStatement
                    | K::CaseSwitchLabel
                    | K::DefaultSwitchLabel
                    | K::CasePatternSwitchLabel
            ) =>
        {
            return statement(false);
        }
        K::ColonToken if parent.kind() == K::BaseList => {
            code.type_only = true;
            code.base_list = true;
            return code;
        }
        K::CommaToken if parent.kind() == K::BaseList => {
            code.type_only = true;
            code.base_list = true;
            return code;
        }
        K::ColonToken | K::CommaToken if parent.kind() == K::TypeParameterConstraintClause => {
            code.constraint = true;
            code.type_only = true;
            return code;
        }
        K::CommaToken if grand_kind == K::TypeParameterConstraintClause => {
            code.constraint = true;
            code.type_only = true;
            return code;
        }
        K::GreaterThanToken
            if parent.kind() == K::TypeParameterList
                && grand
                    .as_ref()
                    .is_some_and(|g| is_type_declaration(g.kind())) =>
        {
            code.where_clause = true;
            return code;
        }
        K::LessThanToken | K::CommaToken if parent.kind() == K::TypeArgumentList => {
            code.type_only = true;
            return code;
        }
        K::OpenParenToken | K::CommaToken
            if matches!(parent.kind(), K::ParameterList | K::BracketedParameterList) =>
        {
            code.type_only = true;
            code.parameter = true;
            return code;
        }
        K::OpenBracketToken if parent.kind() == K::BracketedParameterList => {
            code.type_only = true;
            code.parameter = true;
            return code;
        }
        K::OpenParenToken
            if matches!(
                parent.kind(),
                K::TypeOfExpression | K::SizeOfExpression | K::DefaultExpression
            ) =>
        {
            code.type_only = true;
            code.allows_void = parent.kind() == K::TypeOfExpression;
            return code;
        }
        K::OpenParenToken if parent.kind() == K::CatchDeclaration => {
            code.type_only = true;
            return code;
        }
        K::OpenParenToken
            if matches!(
                parent.kind(),
                K::ForEachStatement | K::ForEachVariableStatement
            ) =>
        {
            code.type_only = true;
            code.allows_var = true;
            return code;
        }
        K::OpenParenToken if matches!(parent.kind(), K::ForStatement | K::UsingStatement) => {
            code.expression = true;
            code.allows_var = true;
            return code;
        }
        K::NewKeyword
            if matches!(
                parent.kind(),
                K::ObjectCreationExpression
                    | K::ArrayCreationExpression
                    | K::ImplicitObjectCreationExpression
            ) =>
        {
            code.type_only = true;
            code.after_new = true;
            return code;
        }
        K::StackAllocKeyword | K::AsKeyword | K::EventKeyword | K::DelegateKeyword
            if !parent.kind().is_expression_node() || parent.kind() == K::AsExpression =>
        {
            code.type_only = true;
            code.allows_void = target.kind() == K::DelegateKeyword;
            return code;
        }
        K::ConstKeyword => {
            code.type_only = true;
            return code;
        }
        K::RefKeyword | K::OutKeyword | K::InKeyword | K::ParamsKeyword | K::ThisKeyword
            if parent.kind() == K::Parameter =>
        {
            code.type_only = true;
            code.parameter = true;
            return code;
        }
        K::OutKeyword if parent.kind() == K::Argument => {
            code.expression = true;
            code.allows_var = true;
            return code;
        }
        K::OperatorKeyword if parent.kind() == K::ConversionOperatorDeclaration => {
            code.type_only = true;
            return code;
        }
        K::IsKeyword | K::CaseKeyword => {
            code.expression = true;
            code.pattern = true;
            return code;
        }
        K::IdentifierToken
            if matches!(
                parent.kind(),
                K::ForEachStatement | K::SingleVariableDesignation
            ) && std::iter::once(parent.clone())
                .chain(parent.ancestors())
                .take(3)
                .any(|node| {
                    node.kind() == K::ForEachStatement || node.kind() == K::ForEachVariableStatement
                }) =>
        {
            code.foreach_in = true;
            return code;
        }
        _ => {}
    }

    // After the last token of a generic type's base list, or of one of its
    // constraints: another `where`.
    if let Some(declaration) = parent
        .ancestors()
        .find(|node| is_type_declaration(node.kind()))
        && declaration.child_of_kind(K::TypeParameterList).is_some()
        && let Some(clause) = std::iter::once(parent.clone())
            .chain(parent.ancestors())
            .find(|node| matches!(node.kind(), K::BaseList | K::TypeParameterConstraintClause))
        && clause
            .last_token_real()
            .is_some_and(|last| last.span() == target.span())
        && clause
            .parent()
            .is_some_and(|p| p.kind() == declaration.kind())
    {
        code.where_clause = true;
        return code;
    }

    let text = target.text();
    // Keywords after which an expression starts.
    if matches!(
        text,
        "return"
            | "throw"
            | "in"
            | "when"
            | "await"
            | "yield"
            | "not"
            | "and"
            | "or"
            | "select"
            | "where"
            | "else"
            | "ref"
    ) || matches!(target.kind(), K::ReturnKeyword | K::ThrowKeyword)
    {
        code.expression = true;
        if text == "not" || text == "and" || text == "or" {
            code.pattern = true;
        }
        return code;
    }

    // Punctuation after which an expression starts.
    let ends_something = match target.kind() {
        K::CloseParenToken
        | K::CloseBracketToken
        | K::CloseBraceToken
        | K::SemicolonToken
        | K::DotToken
        | K::PlusPlusToken
        | K::MinusMinusToken
        | K::MinusGreaterThanToken => true,
        K::GreaterThanToken => parent.kind() == K::TypeArgumentList,
        K::QuestionToken => parent.kind() == K::NullableType,
        K::ExclamationToken => parent.kind() == K::SuppressNullableWarningExpression,
        // `int a, |` is where the next variable's name goes.
        K::CommaToken => parent.kind() == K::VariableDeclaration,
        _ => false,
    };
    let opens_expression = target.kind().is_punctuation() && !ends_something;
    if opens_expression {
        code.expression = true;
        code.argument = matches!(target.kind(), K::OpenParenToken | K::CommaToken)
            && parent.kind() == K::ArgumentList;
        return code;
    }

    // What remains ends an expression: a name, a literal, `)`.
    if target.kind() == K::IdentifierToken
        || target.kind().is_literal_token()
        || matches!(
            target.kind(),
            K::CloseParenToken
                | K::CloseBracketToken
                | K::ThisKeyword
                | K::BaseKeyword
                | K::TrueKeyword
                | K::FalseKeyword
                | K::NullKeyword
                | K::PlusPlusToken
                | K::MinusMinusToken
                | K::GreaterThanToken
        )
        || (target.kind() == K::ExclamationToken
            && parent.kind() == K::SuppressNullableWarningExpression)
    {
        // Up through the names to what holds them: an expression, or a
        // statement that holds one.
        let holder = std::iter::once(parent.clone())
            .chain(parent.ancestors())
            .find(|node| {
                !matches!(
                    node.kind(),
                    K::IdentifierName | K::GenericName | K::QualifiedName | K::TypeArgumentList
                )
            });
        code.after_expression = holder.is_some_and(|holder| {
            holder.kind().is_expression_node()
                || matches!(
                    holder.kind(),
                    K::ExpressionStatement
                        | K::ReturnStatement
                        | K::ThrowStatement
                        | K::YieldReturnStatement
                        | K::IfStatement
                        | K::WhileStatement
                        | K::SwitchStatement
                        | K::LockStatement
                        | K::EqualsValueClause
                        | K::Argument
                        | K::ArrowExpressionClause
                        | K::GlobalStatement
                )
        });
    }
    code
}
