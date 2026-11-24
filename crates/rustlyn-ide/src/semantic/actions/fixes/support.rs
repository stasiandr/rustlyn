//! What every fix that writes code needs: C# text that reads as if the
//! person had typed it.
//!
//! Roslyn builds syntax and hands it to a formatter and a simplifier. There
//! is neither here, so the text is built already formatted: indented the way
//! the file indents, with the file's line breaks, and with every type written
//! as briefly as the `using`s where it goes allow — `int` rather than
//! `System.Int32`, `StringBuilder` where `System.Text` is imported and
//! `System.Text.StringBuilder` where it is not.

use std::collections::HashSet;
use std::path::PathBuf;

use rustlyn_semantics::{Compilation, SpecialType, SymbolId, SymbolKind, Type};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::super::{ActionKind, CodeAction, Context};
use crate::edit::{TextEdit, WorkspaceEdit};
use crate::semantic::View;

// MARK: - layout

/// One level of indentation as the file writes it: a tab if its indented
/// lines start with one, otherwise the smallest run of spaces an indented
/// line starts with, and four spaces when nothing is indented yet.
pub(crate) fn indent_unit(text: &str) -> String {
    let mut smallest: Option<usize> = None;
    for line in text.lines() {
        if line.trim().is_empty() {
            continue;
        }
        if line.starts_with('\t') {
            return "\t".to_string();
        }
        let spaces = line.len() - line.trim_start_matches(' ').len();
        // A continuation line or a doc comment's ` *` can be indented by
        // one; indentation proper is two or more.
        if spaces >= 2 {
            smallest = Some(smallest.map_or(spaces, |at: usize| at.min(spaces)));
        }
    }
    " ".repeat(smallest.unwrap_or(4))
}

/// The line break the file uses.
pub(crate) fn newline(text: &str) -> &'static str {
    if text.contains("\r\n") { "\r\n" } else { "\n" }
}

/// Where the line holding `offset` starts.
pub(crate) fn line_start(text: &str, offset: u32) -> u32 {
    let offset = (offset as usize).min(text.len());
    text[..offset].rfind('\n').map_or(0, |at| at + 1) as u32
}

/// Where the line after the one holding `offset` starts, or the end of the
/// text on the last line.
pub(crate) fn next_line_start(text: &str, offset: u32) -> u32 {
    let offset = (offset as usize).min(text.len());
    text[offset..]
        .find('\n')
        .map_or(text.len(), |at| offset + at + 1) as u32
}

/// The whitespace the line holding `offset` starts with.
pub(crate) fn indentation_at(text: &str, offset: u32) -> String {
    let start = line_start(text, offset) as usize;
    text[start..]
        .chars()
        .take_while(|c| *c == ' ' || *c == '\t')
        .collect()
}

/// Whether only whitespace stands between the start of its line and
/// `offset`: the token there is the first thing on its line.
pub(crate) fn starts_line(text: &str, offset: u32) -> bool {
    let start = line_start(text, offset) as usize;
    text[start..offset as usize].trim().is_empty()
}

/// `block` with every non-empty line indented by `indent`, and with `\n`
/// replaced by the file's line break.
pub(crate) fn indent_lines(block: &str, indent: &str, newline: &str) -> String {
    block
        .split('\n')
        .map(|line| {
            if line.is_empty() {
                String::new()
            } else {
                format!("{indent}{line}")
            }
        })
        .collect::<Vec<_>>()
        .join(newline)
}

/// Where new members go in a type.
#[derive(Clone, Debug)]
pub(crate) enum MemberPlace {
    /// After everything else, before the closing brace.
    End,
    /// Right after this member.
    After(TextSpan),
    /// With the fields: after the last one, or first when there are none.
    Fields,
}

/// The edit that adds `members` to the type declared by `declaration`, in
/// `text`. Each member is written without indentation, with `\n` between
/// its lines and an indent unit of four spaces inside it, which is turned
/// into the file's own. Members are separated by a blank line, except fields
/// among fields.
pub(crate) fn insert_members(
    declaration: &SyntaxNode,
    text: &str,
    members: &[String],
    place: &MemberPlace,
) -> Option<TextEdit> {
    if members.is_empty() {
        return None;
    }
    let open = declaration.child_token_of_kind(SyntaxKind::OpenBraceToken)?;
    let close = declaration.child_token_of_kind(SyntaxKind::CloseBraceToken)?;
    if open.is_missing() || close.is_missing() {
        return None;
    }
    let unit = indent_unit(text);
    let nl = newline(text);
    let outer = indentation_at(text, declaration_start(declaration).start());
    let inner = format!("{outer}{unit}");
    let fields = matches!(place, MemberPlace::Fields);
    let separator = if fields { "\n" } else { "\n\n" };
    let body: Vec<String> = members
        .iter()
        .map(|member| reindent(member, &unit))
        .collect();
    let body = indent_lines(&body.join(separator), &inner, nl);
    let has_members = declaration.children().any(|child| is_member(child.kind()));

    // `class C : I { }` all on one line: the braces go on lines of their
    // own, as the formatter would put them.
    if !text[open.span().end() as usize..close.span().start() as usize].contains('\n') {
        if has_members {
            return None;
        }
        let before = previous_token_end(declaration, &open).unwrap_or(open.span().start());
        return Some(TextEdit::new(
            TextSpan::from_bounds(before, close.span().end()),
            format!("{nl}{outer}{{{nl}{body}{nl}{outer}}}"),
        ));
    }

    match place {
        MemberPlace::After(span) => {
            let at = next_line_start(text, span.end());
            let lead = if at as usize == text.len() && !text.ends_with('\n') {
                nl
            } else {
                ""
            };
            Some(TextEdit::insert(at, format!("{lead}{nl}{body}{nl}")))
        }
        MemberPlace::Fields => {
            let last_field = declaration
                .children()
                .filter(|child| child.kind() == SyntaxKind::FieldDeclaration)
                .last();
            match last_field {
                Some(field) => {
                    let at = next_line_start(text, field.span().end());
                    Some(TextEdit::insert(at, format!("{body}{nl}")))
                }
                None => {
                    let at = next_line_start(text, open.span().end());
                    let gap = if has_members { nl } else { "" };
                    Some(TextEdit::insert(at, format!("{body}{nl}{gap}")))
                }
            }
        }
        MemberPlace::End => {
            let gap = if has_members { nl } else { "" };
            if starts_line(text, close.span().start()) {
                let at = line_start(text, close.span().start());
                Some(TextEdit::insert(at, format!("{gap}{body}{nl}")))
            } else {
                Some(TextEdit::insert(
                    close.span().start(),
                    format!("{nl}{gap}{body}{nl}{outer}"),
                ))
            }
        }
    }
}

/// Four-space indentation inside generated text, turned into the file's.
fn reindent(member: &str, unit: &str) -> String {
    if unit == "    " {
        return member.to_string();
    }
    member
        .split('\n')
        .map(|line| {
            let spaces = line.len() - line.trim_start_matches(' ').len();
            format!(
                "{}{}",
                unit.repeat(spaces / 4),
                &line[spaces - spaces % 4..]
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// The first token of a declaration past its attributes and doc comment:
/// the line it is indented by.
fn declaration_start(declaration: &SyntaxNode) -> TextSpan {
    declaration
        .first_token()
        .map_or(declaration.span(), |token| token.span())
}

fn previous_token_end(declaration: &SyntaxNode, token: &SyntaxToken) -> Option<u32> {
    declaration
        .descendant_tokens()
        .take_while(|candidate| candidate.span().start() < token.span().start())
        .filter(|candidate| !candidate.is_missing())
        .last()
        .map(|candidate| candidate.span().end())
}

/// Whether a node is a member of a type declaration.
pub(crate) const fn is_member(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::MethodDeclaration
            | SyntaxKind::FieldDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::EventDeclaration
            | SyntaxKind::EventFieldDeclaration
            | SyntaxKind::IndexerDeclaration
            | SyntaxKind::ConstructorDeclaration
            | SyntaxKind::DestructorDeclaration
            | SyntaxKind::OperatorDeclaration
            | SyntaxKind::ConversionOperatorDeclaration
            | SyntaxKind::ClassDeclaration
            | SyntaxKind::StructDeclaration
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::RecordDeclaration
            | SyntaxKind::RecordStructDeclaration
            | SyntaxKind::EnumDeclaration
            | SyntaxKind::DelegateDeclaration
            | SyntaxKind::EnumMemberDeclaration
    )
}

/// Whether a node declares a type with a body of members.
pub(crate) const fn is_type_declaration(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::ClassDeclaration
            | SyntaxKind::StructDeclaration
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::RecordDeclaration
            | SyntaxKind::RecordStructDeclaration
    )
}

// MARK: - declarations

/// A type's declaration, as a place to write new members into.
pub(crate) struct Declaration {
    /// The file it is in, or `None` for the file asked about.
    pub path: Option<PathBuf>,
    /// The type declaration, from that file's tree.
    pub node: SyntaxNode,
    /// That file's text: the editor's for the file asked about, the
    /// compiled one for any other.
    pub text: String,
}

impl Declaration {
    /// An action whose edits are to this declaration's file.
    pub(crate) fn action(
        &self,
        context: &Context<'_, '_>,
        title: impl Into<String>,
        kind: ActionKind,
        fixes: Option<&str>,
        edits: Vec<TextEdit>,
    ) -> CodeAction {
        match &self.path {
            None => context.local(title, kind, fixes, edits),
            Some(path) => CodeAction {
                title: title.into(),
                kind,
                fixes: fixes.map(str::to_owned),
                edit: WorkspaceEdit::single(path.clone(), edits),
            },
        }
    }
}

/// Where `symbol`, a type declared in the project, is declared: in the file
/// asked about when one of its parts is, which is `text` there.
pub(crate) fn declaration_of(view: &View<'_>, symbol: SymbolId, text: &str) -> Option<Declaration> {
    let compilation = view.compilation();
    let places = compilation.declaration_nodes(symbol);
    let &(tree, span) = places
        .iter()
        .find(|(tree, _)| *tree == view.tree)
        .or_else(|| places.first())?;
    if tree == view.tree {
        let span = match &view.speculation {
            Some(speculation) => speculation.unmap(span)?,
            None => span,
        };
        let node = view.root.find_node(span)?;
        return is_type_declaration(node.kind()).then(|| Declaration {
            path: None,
            node,
            text: text.to_string(),
        });
    }
    let path = view.semantic.path_of(tree)?.to_path_buf();
    let text = view.semantic.text(&path)?.to_string();
    let node = compilation.trees().get(tree)?.root().find_node(span)?;
    is_type_declaration(node.kind()).then_some(Declaration {
        path: Some(path),
        node,
        text,
    })
}

// MARK: - inference

/// One argument of a call, as the parameter that would take it.
#[derive(Clone, Debug)]
pub(crate) struct Argument {
    /// `ref `, `out `, `in ` or nothing.
    pub modifier: &'static str,
    pub ty: Type,
    pub name: String,
}

/// The parameters a method would need to take the arguments of `list`, an
/// `ArgumentList`: typed as the arguments are, and named after them the way
/// Roslyn's `GenerateNameForArgument` does — the name of a named argument, a
/// variable's or member's own name, a type's name for a value of that type,
/// and `v` for anything else — numbered where names repeat.
pub(crate) fn arguments_of(view: &mut View<'_>, list: &SyntaxNode) -> Vec<Argument> {
    let mut found = Vec::new();
    let mut names = Vec::new();
    for argument in list
        .children()
        .filter(|child| child.kind() == SyntaxKind::Argument)
    {
        let modifier = if argument
            .child_token_of_kind(SyntaxKind::RefKeyword)
            .is_some()
        {
            "ref "
        } else if argument
            .child_token_of_kind(SyntaxKind::OutKeyword)
            .is_some()
        {
            "out "
        } else if argument
            .child_token_of_kind(SyntaxKind::InKeyword)
            .is_some()
        {
            "in "
        } else {
            ""
        };
        let Some(expression) = argument
            .children()
            .filter(|child| child.kind() != SyntaxKind::NameColon)
            .last()
        else {
            continue;
        };
        let ty = if expression.kind() == SyntaxKind::DeclarationExpression {
            match expression
                .children()
                .find(|child| child.kind().is_type_node())
            {
                Some(written) if written.text().trim() != "var" => {
                    view.model.type_of_syntax(&written)
                }
                _ => Type::Error,
            }
        } else {
            view.type_of(&expression)
        };
        let named = argument
            .child_of_kind(SyntaxKind::NameColon)
            .and_then(|colon| {
                colon
                    .descendant_tokens()
                    .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                    .map(|token| token.value_text().to_string())
            });
        let name = named.unwrap_or_else(|| name_for(view, &expression, &ty));
        names.push(name);
        found.push(Argument {
            modifier,
            ty,
            name: String::new(),
        });
    }
    for (argument, name) in found.iter_mut().zip(unique_names(names, &[])) {
        argument.name = escape_keyword(&name);
    }
    found
}

/// What a parameter or variable holding `expression` would be called.
fn name_for(view: &View<'_>, expression: &SyntaxNode, ty: &Type) -> String {
    let last_identifier = |node: &SyntaxNode| {
        node.descendant_tokens()
            .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
            .last()
            .map(|token| token.value_text().to_string())
    };
    match expression.kind() {
        SyntaxKind::IdentifierName => {
            if let Some(name) = last_identifier(expression) {
                return camel(&name);
            }
        }
        SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::DeclarationExpression => {
            if let Some(name) = last_identifier(expression) {
                return camel(&name);
            }
        }
        SyntaxKind::InvocationExpression => {
            if let Some(callee) = expression.children().next()
                && let Some(name) = last_identifier(&callee)
            {
                let name = name
                    .strip_prefix("Get")
                    .filter(|rest| rest.starts_with(char::is_uppercase))
                    .unwrap_or(&name);
                return camel(name);
            }
        }
        _ => {}
    }
    let symbols = view.compilation().symbols();
    match ty {
        Type::Named { symbol, .. } => {
            let qualified = symbols.qualified_name(*symbol);
            if SpecialType::ALL
                .iter()
                .any(|special| special.metadata_name() == qualified)
            {
                "v".to_string()
            } else {
                let name = &symbols.get(*symbol).name;
                // `IDisposable` is a disposable.
                let name = name
                    .strip_prefix('I')
                    .filter(|rest| rest.starts_with(char::is_uppercase))
                    .unwrap_or(name);
                camel(name)
            }
        }
        _ => "v".to_string(),
    }
}

/// The type the code around `expression` wants it to have: the declared
/// type it initializes, the other side of an assignment, what the member
/// returns, `bool` for a condition, the other operand of arithmetic, `void`
/// for a statement of its own; `Type::Error` when nothing says, which is
/// written as `object`.
pub(crate) fn expected_type(view: &mut View<'_>, expression: &SyntaxNode) -> Type {
    let Some(parent) = expression.parent().cloned() else {
        return Type::Error;
    };
    let first = parent.children().next();
    match parent.kind() {
        SyntaxKind::ParenthesizedExpression => expected_type(view, &parent),
        SyntaxKind::ExpressionStatement => Type::Void,
        SyntaxKind::EqualsValueClause => {
            let Some(holder) = parent.parent().cloned() else {
                return Type::Error;
            };
            let declared = match holder.kind() {
                SyntaxKind::VariableDeclarator => holder.parent().cloned(),
                SyntaxKind::PropertyDeclaration | SyntaxKind::Parameter => Some(holder),
                _ => None,
            };
            match declared
                .and_then(|node| node.children().find(|child| child.kind().is_type_node()))
            {
                Some(written) if written.text().trim() != "var" => {
                    view.model.type_of_syntax(&written)
                }
                _ => Type::Error,
            }
        }
        kind if is_assignment(kind) => {
            let other = if first.as_ref() == Some(expression) {
                parent.children().last()
            } else {
                first
            };
            other.map_or(Type::Error, |other| usable(view.type_of(&other)))
        }
        SyntaxKind::ReturnStatement | SyntaxKind::ArrowExpressionClause => {
            let context = view.model.binder().context_at(view.tree, &parent);
            match context.enclosing_member() {
                Some(member) => {
                    let symbols = view.compilation().symbols();
                    let ty = view.model.type_of_symbol(member);
                    // An `async` method returns its `Task`'s argument.
                    if symbols
                        .get(member)
                        .modifiers
                        .contains(rustlyn_semantics::Modifiers::ASYNC)
                    {
                        match ty {
                            Type::Named { type_arguments, .. } if type_arguments.len() == 1 => {
                                type_arguments[0].clone()
                            }
                            _ => Type::Error,
                        }
                    } else {
                        ty
                    }
                }
                None => Type::Error,
            }
        }
        SyntaxKind::IfStatement | SyntaxKind::WhileStatement | SyntaxKind::DoStatement
            if expression.kind() != SyntaxKind::Block =>
        {
            special(view, SpecialType::Boolean)
        }
        SyntaxKind::LogicalNotExpression
        | SyntaxKind::LogicalAndExpression
        | SyntaxKind::LogicalOrExpression => special(view, SpecialType::Boolean),
        SyntaxKind::ConditionalExpression if first.as_ref() == Some(expression) => {
            special(view, SpecialType::Boolean)
        }
        SyntaxKind::AddExpression
        | SyntaxKind::SubtractExpression
        | SyntaxKind::MultiplyExpression
        | SyntaxKind::DivideExpression
        | SyntaxKind::ModuloExpression
        | SyntaxKind::EqualsExpression
        | SyntaxKind::NotEqualsExpression
        | SyntaxKind::LessThanExpression
        | SyntaxKind::GreaterThanExpression
        | SyntaxKind::LessThanOrEqualExpression
        | SyntaxKind::GreaterThanOrEqualExpression => {
            let other = if first.as_ref() == Some(expression) {
                parent.children().last()
            } else {
                first
            };
            other.map_or(Type::Error, |other| usable(view.type_of(&other)))
        }
        _ => Type::Error,
    }
}

/// `null` has no type to write down.
fn usable(ty: Type) -> Type {
    match ty {
        Type::Null => Type::Error,
        other => other,
    }
}

fn special(view: &View<'_>, special: SpecialType) -> Type {
    view.compilation()
        .special_type(special)
        .map_or(Type::Error, Type::named)
}

/// Whether a node kind is `=` or a compound assignment.
pub(crate) const fn is_assignment(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::SimpleAssignmentExpression
            | SyntaxKind::AddAssignmentExpression
            | SyntaxKind::SubtractAssignmentExpression
            | SyntaxKind::MultiplyAssignmentExpression
            | SyntaxKind::DivideAssignmentExpression
            | SyntaxKind::ModuloAssignmentExpression
            | SyntaxKind::AndAssignmentExpression
            | SyntaxKind::OrAssignmentExpression
            | SyntaxKind::ExclusiveOrAssignmentExpression
            | SyntaxKind::CoalesceAssignmentExpression
    )
}

// MARK: - names

/// Writes types the way they read at one place in a file: keywords for the
/// built-in types, `T?` for a nullable value, and each named type with as
/// little of its namespace as the `using`s there make necessary.
pub(crate) struct Namer<'c> {
    compilation: &'c Compilation,
    /// The namespaces a simple name is looked up in: the global one, those
    /// the code is declared in and those it imports.
    namespaces: HashSet<SymbolId>,
    /// The types the code is written in, whose nested types need no prefix.
    enclosing: HashSet<SymbolId>,
}

impl<'c> Namer<'c> {
    /// A namer for the code at `node` of the view's file.
    pub(crate) fn at(view: &View<'c>, node: &SyntaxNode) -> Self {
        let compilation = view.compilation();
        let mut namespaces: HashSet<SymbolId> =
            view.namespaces_in_scope(node).into_iter().collect();
        namespaces.insert(compilation.global_namespace());
        Self {
            compilation,
            namespaces,
            enclosing: view.enclosing_types(node),
        }
    }

    /// A namer for a file that does not exist yet: nothing is imported but
    /// the namespaces it will declare and import.
    pub(crate) fn with_namespaces(compilation: &'c Compilation, namespaces: &[SymbolId]) -> Self {
        let mut namespaces: HashSet<SymbolId> = namespaces.iter().copied().collect();
        namespaces.insert(compilation.global_namespace());
        Self {
            compilation,
            namespaces,
            enclosing: HashSet::new(),
        }
    }

    /// Whether the namespace called `name` is imported, or is one the code
    /// is inside.
    pub(crate) fn imports(&self, name: &str) -> bool {
        let symbols = self.compilation.symbols();
        self.namespaces
            .iter()
            .any(|namespace| symbols.qualified_name(*namespace) == name)
    }

    /// `throw new NotImplementedException();`, qualified unless `System` is
    /// imported.
    pub(crate) fn not_implemented(&self) -> String {
        if self.imports("System") {
            "throw new NotImplementedException();".to_string()
        } else {
            "throw new System.NotImplementedException();".to_string()
        }
    }

    /// The same, as an expression: `throw new NotImplementedException()`.
    pub(crate) fn not_implemented_expression(&self) -> String {
        self.not_implemented().trim_end_matches(';').to_string()
    }

    /// How `ty` is written here.
    pub(crate) fn name(&self, ty: &Type) -> String {
        let symbols = self.compilation.symbols();
        match ty {
            Type::Error | Type::Null => "object".to_string(),
            Type::Void => "void".to_string(),
            Type::Dynamic => "dynamic".to_string(),
            Type::TypeParameter(symbol) => symbols.get(*symbol).name.clone(),
            Type::Pointer(inner) => format!("{}*", self.name(inner)),
            Type::ByRef(inner) => self.name(inner),
            Type::FunctionPointer(_) => ty.display(symbols),
            Type::Array { element, rank } => {
                format!(
                    "{}[{}]",
                    self.name(element),
                    ",".repeat(rank.saturating_sub(1))
                )
            }
            Type::Tuple(elements) => {
                let parts: Vec<String> = elements
                    .iter()
                    .map(|element| match &element.name {
                        Some(name) => format!("{} {name}", self.name(&element.ty)),
                        None => self.name(&element.ty),
                    })
                    .collect();
                format!("({})", parts.join(", "))
            }
            Type::Named {
                symbol,
                type_arguments,
            } => {
                let qualified = symbols.qualified_name(*symbol);
                if let Some(special) = SpecialType::ALL
                    .iter()
                    .find(|special| special.metadata_name() == qualified)
                {
                    return special.keyword().to_string();
                }
                if qualified == "System.Nullable`1"
                    && let [inner] = type_arguments.as_slice()
                {
                    return format!("{}?", self.name(inner));
                }
                let name = self.symbol_name(*symbol);
                if type_arguments.is_empty() {
                    name
                } else {
                    let arguments: Vec<String> =
                        type_arguments.iter().map(|ty| self.name(ty)).collect();
                    format!("{name}<{}>", arguments.join(", "))
                }
            }
        }
    }

    /// A type's name without its type arguments, with what it needs in front
    /// of it here: nothing when it is in scope, its namespace or the type it
    /// is nested in otherwise.
    pub(crate) fn symbol_name(&self, symbol: SymbolId) -> String {
        let symbols = self.compilation.symbols();
        let found = symbols.get(symbol);
        let Some(container) = found.container else {
            return found.name.clone();
        };
        match symbols.get(container).kind {
            SymbolKind::NamedType if !self.enclosing.contains(&container) => {
                format!("{}.{}", self.symbol_name(container), found.name)
            }
            SymbolKind::Namespace if !self.namespaces.contains(&container) => {
                format!("{}.{}", symbols.qualified_name(container), found.name)
            }
            _ => found.name.clone(),
        }
    }
}

// MARK: - using directives

/// The edit that adds `using namespace;` to the file whose root is `root`:
/// among the `using`s already there, in order, `System` ones first — where
/// Roslyn puts it by default — or above the first declaration when there
/// are none.
pub(crate) fn add_using(root: &SyntaxNode, text: &str, namespace: &str) -> Option<TextEdit> {
    let nl = newline(text);
    let plain = |using: &SyntaxNode| {
        using.child_of_kind(SyntaxKind::NameEquals).is_none()
            && using
                .child_token_of_kind(SyntaxKind::StaticKeyword)
                .is_none()
            && using
                .child_token_of_kind(SyntaxKind::GlobalKeyword)
                .is_none()
    };
    // The `using`s of the file, or of its first namespace when the file
    // keeps them inside.
    let mut scope = root.clone();
    let mut usings: Vec<SyntaxNode> = scope
        .children()
        .filter(|child| child.kind() == SyntaxKind::UsingDirective)
        .collect();
    if usings.is_empty()
        && let Some(namespace) = root.children().find(|child| {
            matches!(
                child.kind(),
                SyntaxKind::NamespaceDeclaration | SyntaxKind::FileScopedNamespaceDeclaration
            )
        })
    {
        let inside: Vec<SyntaxNode> = namespace
            .children()
            .filter(|child| child.kind() == SyntaxKind::UsingDirective)
            .collect();
        if !inside.is_empty() {
            scope = namespace;
            usings = inside;
        }
    }
    let _ = scope;
    let name_of = |using: &SyntaxNode| {
        using
            .children()
            .find(|child| child.kind().is_type_node())
            .map(|name| name.text().trim().to_string())
            .unwrap_or_default()
    };
    if usings
        .iter()
        .any(|using| plain(using) && name_of(using) == namespace)
    {
        return None;
    }
    let key = crate::editorconfig::using_sort_key;
    let wanted = key(namespace);
    let plain_usings: Vec<&SyntaxNode> = usings.iter().filter(|using| plain(using)).collect();
    if let Some(first) = usings.first() {
        let indent = indentation_at(text, first.span().start());
        let line = format!("{indent}using {namespace};{nl}");
        let before = plain_usings
            .iter()
            .find(|using| key(&name_of(using)) > wanted)
            .copied();
        return Some(match before {
            Some(using) => TextEdit::insert(line_start(text, using.span().start()), line),
            None => {
                let last = plain_usings.last().copied().unwrap_or(usings.last()?);
                let at = next_line_start(text, last.span().end());
                if at as usize == text.len() && !text.ends_with('\n') {
                    TextEdit::insert(at, format!("{nl}{indent}using {namespace};"))
                } else {
                    TextEdit::insert(at, line)
                }
            }
        });
    }
    // No `using`s at all, and `csharp_using_directive_placement` wants them
    // inside the namespace: the first line inside the file's namespace.
    if crate::editorconfig::current_code_style().using_placement
        == Some(crate::editorconfig::UsingPlacement::InsideNamespace)
        && let Some(holder) = root.children().find(|child| {
            matches!(
                child.kind(),
                SyntaxKind::NamespaceDeclaration | SyntaxKind::FileScopedNamespaceDeclaration
            )
        })
    {
        if holder.kind() == SyntaxKind::FileScopedNamespaceDeclaration {
            let semicolon = holder.child_token_of_kind(SyntaxKind::SemicolonToken)?;
            let at = next_line_start(text, semicolon.span().end());
            return Some(TextEdit::insert(at, format!("{nl}using {namespace};{nl}")));
        }
        let open = holder.child_token_of_kind(SyntaxKind::OpenBraceToken)?;
        let at = next_line_start(text, open.span().end());
        let indent = indentation_at(text, holder.span().start());
        let unit = if text.contains("\n\t") { "\t" } else { "    " };
        return Some(TextEdit::insert(
            at,
            format!("{indent}{unit}using {namespace};{nl}{nl}"),
        ));
    }
    // No `using`s at all: one above the first thing in the file, past any
    // header comment, with a blank line after it.
    let first = root
        .children()
        .find(|child| child.kind() != SyntaxKind::ExternAliasDirective)
        .and_then(|child| child.first_token());
    let at = first.map_or(0, |token| line_start(text, token.span().start()));
    Some(TextEdit::insert(at, format!("using {namespace};{nl}{nl}")))
}

// MARK: - words

/// How far apart two names are, if they are close enough for one to be a
/// misspelling of the other.
///
/// Roslyn's `WordSimilarityChecker`: names shorter than three characters
/// are never similar, since everything short is close to everything else;
/// the same name in another case is the closest there is; otherwise the
/// edit distance, counting a swap of two neighbours as one edit, must be at
/// most one for a name of four characters or fewer and two for a longer one.
pub(crate) fn similarity(source: &str, candidate: &str) -> Option<u32> {
    let length = source.chars().count();
    if length < 3 || source == candidate {
        return None;
    }
    let threshold = if length <= 4 { 1 } else { 2 };
    let other = candidate.chars().count();
    if length.abs_diff(other) > threshold {
        return None;
    }
    if source.eq_ignore_ascii_case(candidate) {
        return Some(0);
    }
    let distance = edit_distance(source, candidate);
    (distance <= threshold).then_some(distance as u32)
}

/// Damerau–Levenshtein distance, the restricted kind: insertions, deletions,
/// substitutions and swaps of adjacent characters each cost one.
fn edit_distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let mut table = vec![vec![0usize; b.len() + 1]; a.len() + 1];
    for (i, row) in table.iter_mut().enumerate() {
        row[0] = i;
    }
    for (j, cell) in table[0].iter_mut().enumerate() {
        *cell = j;
    }
    for i in 1..=a.len() {
        for j in 1..=b.len() {
            let cost = usize::from(a[i - 1] != b[j - 1]);
            let mut best = (table[i - 1][j] + 1)
                .min(table[i][j - 1] + 1)
                .min(table[i - 1][j - 1] + cost);
            if i > 1 && j > 1 && a[i - 1] == b[j - 2] && a[i - 2] == b[j - 1] {
                best = best.min(table[i - 2][j - 2] + 1);
            }
            table[i][j] = best;
        }
    }
    table[a.len()][b.len()]
}

/// `name` with its first letter lower-cased: what a parameter or local
/// holding a `name` is called.
pub(crate) fn camel(name: &str) -> String {
    let mut chars = name.chars();
    match chars.next() {
        Some(first) => first.to_lowercase().chain(chars).collect(),
        None => String::new(),
    }
}

/// Names made unique the way Roslyn's `NameGenerator` does it: every name
/// that occurs more than once gets a number, counting from one.
pub(crate) fn unique_names(names: Vec<String>, taken: &[String]) -> Vec<String> {
    let mut out = Vec::with_capacity(names.len());
    let mut counters: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
    for name in &names {
        let repeated =
            names.iter().filter(|other| *other == name).count() > 1 || taken.contains(name);
        if repeated {
            let counter = counters.entry(name.clone()).or_insert(0);
            loop {
                *counter += 1;
                let candidate = format!("{name}{counter}");
                if !taken.contains(&candidate) && !names.contains(&candidate) {
                    out.push(candidate);
                    break;
                }
            }
        } else {
            out.push(name.clone());
        }
    }
    out
}

/// Whether a word is a C# keyword and so needs an `@` to be a name.
pub(crate) fn escape_keyword(name: &str) -> String {
    const KEYWORDS: &[&str] = &[
        "abstract",
        "as",
        "base",
        "bool",
        "break",
        "byte",
        "case",
        "catch",
        "char",
        "checked",
        "class",
        "const",
        "continue",
        "decimal",
        "default",
        "delegate",
        "do",
        "double",
        "else",
        "enum",
        "event",
        "explicit",
        "extern",
        "false",
        "finally",
        "fixed",
        "float",
        "for",
        "foreach",
        "goto",
        "if",
        "implicit",
        "in",
        "int",
        "interface",
        "internal",
        "is",
        "lock",
        "long",
        "namespace",
        "new",
        "null",
        "object",
        "operator",
        "out",
        "override",
        "params",
        "private",
        "protected",
        "public",
        "readonly",
        "ref",
        "return",
        "sbyte",
        "sealed",
        "short",
        "sizeof",
        "stackalloc",
        "static",
        "string",
        "struct",
        "switch",
        "this",
        "throw",
        "true",
        "try",
        "typeof",
        "uint",
        "ulong",
        "unchecked",
        "unsafe",
        "ushort",
        "using",
        "virtual",
        "void",
        "volatile",
        "while",
    ];
    if KEYWORDS.contains(&name) {
        format!("@{name}")
    } else {
        name.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn indentation_follows_the_file() {
        assert_eq!(indent_unit("class C\n{\n  int x;\n}\n"), "  ");
        assert_eq!(indent_unit("class C\n{\n\tint x;\n}\n"), "\t");
        assert_eq!(indent_unit("class C {}"), "    ");
        assert_eq!(reindent("a\n    b\n        c", "\t"), "a\n\tb\n\t\tc");
    }

    #[test]
    fn misspellings_are_near() {
        assert_eq!(similarity("WriteLin", "WriteLine"), Some(1));
        assert_eq!(similarity("cout", "count"), Some(1));
        assert_eq!(similarity("Lenght", "Length"), Some(1));
        assert_eq!(similarity("name", "NAME"), Some(0));
        assert_eq!(similarity("ab", "abc"), None);
        assert_eq!(similarity("Frobnicate", "Count"), None);
    }

    #[test]
    fn repeated_names_are_numbered() {
        assert_eq!(
            unique_names(vec!["v".into(), "v".into(), "name".into()], &[]),
            ["v1", "v2", "name"]
        );
    }
}
