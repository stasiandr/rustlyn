//! Change signature: reorder, remove and add the parameters of a method or
//! constructor, and every call of it with them.
//!
//! Roslyn's `ChangeSignature` service, which Visual Studio drives through a
//! dialog. The dialog shows the parameters ([`Semantic::change_signature_info`])
//! and hands back the new list, each entry an old parameter by its index or
//! a new one ([`ChangeParam`]); [`Semantic::change_signature`] then rewrites:
//!
//! * the declaration, and every declaration in its family — the members it
//!   overrides or implements and those that override or implement it — each
//!   keeping its own parameter names, attributes, modifiers and defaults;
//! * each declaration's `<param>` documentation, in the new order, with an
//!   empty one for a new parameter where the others are documented;
//! * every call across the project: positional arguments move, named ones
//!   keep their names, an argument for a removed parameter goes, and a new
//!   parameter gets the value the dialog gave for call sites. Once an
//!   argument is left out — an optional parameter a call did not pass, or a
//!   new optional one with no call-site value — the ones after it are
//!   written with their names, since their positions no longer say which
//!   parameter they are for;
//! * `params` arguments stay together; the receiver of an extension method
//!   called as `x.M()` is its `this` argument, which stays first;
//! * `new T(...)`, target-typed `new(...)`, attribute usages, and
//!   `: base(...)` and `: this(...)` initializers of a constructor.
//!
//! A call through a delegate the method was converted to is not a call of
//! the method, and is left alone, as a method group is.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use rustlyn_semantics::{BoundStatementKind, MethodKind, SymbolId, SymbolKind};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::super::Context;
use super::super::text::{is_identifier, line_start, newline};
use super::sources::{project_files, root_of, text_of, token_at, with_context, with_view};
use crate::edit::{TextEdit, WorkspaceEdit};
use crate::semantic::{ReferenceKind, Semantic};

/// One parameter of the changed signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChangeParam {
    /// The parameter that is at this index now.
    Existing(usize),
    /// A parameter that was not there.
    Added(AddedParameter),
}

/// A new parameter, as the dialog's "Add" page describes it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AddedParameter {
    /// Its type, as it is to be written: `int`, `List<string>`.
    pub ty: String,
    pub name: String,
    /// Its default value, which makes it optional.
    pub default: Option<String>,
    /// What every existing call passes for it. With none, a call passes
    /// nothing when the parameter is optional and `default` otherwise.
    pub call_site: Option<String>,
}

/// One parameter as it is now, for the dialog to list.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SignatureParameter {
    /// `ref `, `out `, `in `, `this `, `params ` or nothing.
    pub modifier: String,
    /// The type as written.
    pub ty: String,
    pub name: String,
    /// The default value as written, for an optional parameter.
    pub default: Option<String>,
}

/// What a change of signature would change: the member, and its parameters
/// as they are.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SignatureTarget {
    /// The member as one line: `Shop.Buy(string item, int count)`.
    pub display: String,
    pub parameters: Vec<SignatureParameter>,
    /// Whether the first parameter cannot move: an extension method's
    /// `this`.
    pub first_is_fixed: bool,
}

impl Semantic {
    /// The method or constructor at `offset` of `path` — its declaration,
    /// or a call of it — with its parameters, for the change-signature
    /// dialog.
    ///
    /// # Errors
    ///
    /// Why the signature there cannot be changed.
    pub fn change_signature_info(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
    ) -> Result<SignatureTarget, String> {
        with_context(self, path, text, TextSpan::new(offset, 0), |context| {
            let target = target_at(context, offset)?;
            Ok(info_of(context, &target))
        })
        .ok_or_else(|| "The file is not part of the project.".to_string())?
    }

    /// Changes the signature of the method or constructor at `offset` of
    /// `path` to `order`, and every declaration and call of it.
    ///
    /// # Errors
    ///
    /// Why the change cannot be made: not a method, an index out of range,
    /// a `params` parameter that is not last, a required parameter after an
    /// optional one, a call it cannot rewrite.
    pub fn change_signature(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
        order: &[ChangeParam],
    ) -> Result<WorkspaceEdit, String> {
        with_context(self, path, text, TextSpan::new(offset, 0), |context| {
            let target = target_at(context, offset)?;
            change(context, &target, order)
        })
        .ok_or_else(|| "The file is not part of the project.".to_string())?
    }
}

/// The member whose signature is being changed, and a name token of it in
/// the file asked about, to find its references from.
pub(super) struct Target {
    pub symbol: SymbolId,
    pub name_offset: u32,
}

/// The method or constructor at `offset`: the declaration it is in (outside
/// its body) or the call it is on.
pub(super) fn target_at(context: &mut Context<'_, '_>, offset: u32) -> Result<Target, String> {
    let refuse = || "Place the cursor on a method or constructor, or on a call of one.".to_string();
    let root = context.view.syntax_root().clone();
    let token = root
        .find_token(offset)
        .filter(|token| token.span().contains(offset))
        .or_else(|| root.find_token(offset.checked_sub(1)?))
        .ok_or_else(refuse)?;
    let mut name: Option<SyntaxToken> = None;
    for node in std::iter::once(token.parent().clone()).chain(token.parent().ancestors()) {
        match node.kind() {
            SyntaxKind::Block | SyntaxKind::ArrowExpressionClause => {
                if name.is_none() && !is_call_name(&token) {
                    return Err(refuse());
                }
            }
            SyntaxKind::MethodDeclaration | SyntaxKind::ConstructorDeclaration => {
                name = name.or_else(|| node.child_token_of_kind(SyntaxKind::IdentifierToken));
                break;
            }
            SyntaxKind::InvocationExpression => {
                if let Some(called) = node
                    .children()
                    .next()
                    .and_then(|callee| rightmost_name(&callee))
                {
                    name = Some(called);
                    break;
                }
            }
            SyntaxKind::ObjectCreationExpression => {
                if let Some(ty) = node.children().find(|child| child.kind().is_type_node())
                    && let Some(called) = rightmost_name(&ty)
                {
                    name = Some(called);
                    break;
                }
            }
            _ if is_type_declaration_kind(node.kind()) => break,
            _ => {}
        }
    }
    let name = name.ok_or_else(refuse)?;
    let resolved = context.view.resolve(&name).ok_or_else(refuse)?;
    let crate::semantic::Resolved::Symbol(symbol) = resolved else {
        return Err(refuse());
    };
    let semantic = context.view.project();
    let found = semantic.compilation.symbols().get(symbol);
    let is_method = found.kind == SymbolKind::Method
        && found.as_method().is_some_and(|method| {
            matches!(
                method.method_kind,
                MethodKind::Ordinary | MethodKind::Constructor
            )
        });
    if !is_method {
        return Err(refuse());
    }
    if semantic.compilation.is_from_metadata(symbol) || found.locations.is_empty() {
        return Err(format!(
            "'{}' is not declared in the project, so its signature cannot change.",
            found.name
        ));
    }
    Ok(Target {
        symbol,
        name_offset: name.span().start(),
    })
}

fn is_type_declaration_kind(kind: SyntaxKind) -> bool {
    super::super::text::is_type_declaration(kind)
}

/// Whether `token` is the name of something called, inside a body: the
/// cursor is on a call there.
fn is_call_name(token: &SyntaxToken) -> bool {
    token.kind() == SyntaxKind::IdentifierToken
        && token.parent().ancestors().any(|node| {
            matches!(
                node.kind(),
                SyntaxKind::InvocationExpression | SyntaxKind::ObjectCreationExpression
            )
        })
}

/// The name token at the right of a callee: `M` of `a.b.M<T>`.
fn rightmost_name(node: &SyntaxNode) -> Option<SyntaxToken> {
    match node.kind() {
        SyntaxKind::IdentifierName | SyntaxKind::GenericName => {
            node.child_token_of_kind(SyntaxKind::IdentifierToken)
        }
        SyntaxKind::SimpleMemberAccessExpression
        | SyntaxKind::MemberBindingExpression
        | SyntaxKind::QualifiedName
        | SyntaxKind::AliasQualifiedName => rightmost_name(&node.children().last()?),
        _ => None,
    }
}

fn info_of(context: &Context<'_, '_>, target: &Target) -> SignatureTarget {
    let semantic = context.view.project();
    let symbols = semantic.compilation.symbols();
    let method = symbols.get(target.symbol);
    let declaration = declaration_node(context, target.symbol);
    let parameters: Vec<SignatureParameter> = declaration
        .as_ref()
        .and_then(|node| node.child_of_kind(SyntaxKind::ParameterList))
        .map(|list| {
            list.children()
                .filter(|child| child.kind() == SyntaxKind::Parameter)
                .map(|parameter| describe_parameter(&parameter))
                .collect()
        })
        .unwrap_or_default();
    let container = method
        .container
        .map(|container| symbols.get(container).name.clone())
        .unwrap_or_default();
    let is_constructor = method
        .as_method()
        .is_some_and(|detail| detail.method_kind == MethodKind::Constructor);
    let name = if is_constructor {
        container.clone()
    } else {
        format!("{container}.{}", method.name)
    };
    let list: Vec<String> = parameters
        .iter()
        .map(|parameter| format!("{}{} {}", parameter.modifier, parameter.ty, parameter.name))
        .collect();
    SignatureTarget {
        display: format!("{name}({})", list.join(", ")),
        first_is_fixed: method.as_method().is_some_and(|detail| detail.is_extension),
        parameters,
    }
}

fn describe_parameter(parameter: &SyntaxNode) -> SignatureParameter {
    let modifier: String = parameter
        .child_tokens()
        .filter(|token| {
            matches!(
                token.kind(),
                SyntaxKind::RefKeyword
                    | SyntaxKind::OutKeyword
                    | SyntaxKind::InKeyword
                    | SyntaxKind::ThisKeyword
                    | SyntaxKind::ParamsKeyword
            )
        })
        .map(|token| format!("{} ", token.text()))
        .collect();
    SignatureParameter {
        modifier,
        ty: parameter
            .children()
            .find(|child| child.kind().is_type_node())
            .map(|ty| ty.text())
            .unwrap_or_default(),
        name: parameter
            .child_token_of_kind(SyntaxKind::IdentifierToken)
            .map(|token| token.value_text().to_string())
            .unwrap_or_default(),
        default: parameter
            .child_of_kind(SyntaxKind::EqualsValueClause)
            .and_then(|clause| clause.children().next())
            .map(|value| value.text()),
    }
}

/// The declaration of a member of the project, from its file's tree.
pub(super) fn declaration_node(context: &Context<'_, '_>, symbol: SymbolId) -> Option<SyntaxNode> {
    let semantic = context.view.project();
    let location = semantic
        .compilation
        .symbols()
        .get(symbol)
        .locations
        .first()
        .copied()?;
    let path = semantic.path_of(location.tree)?.to_path_buf();
    let root = root_of(context, &path)?;
    let span = if path == context.path {
        match &context.view.speculation {
            Some(speculation) => speculation.unmap(location.span)?,
            None => location.span,
        }
    } else {
        location.span
    };
    let token = root.find_token(span.start())?;
    std::iter::once(token.parent().clone())
        .chain(token.parent().ancestors())
        .find(|node| {
            matches!(
                node.kind(),
                SyntaxKind::MethodDeclaration | SyntaxKind::ConstructorDeclaration
            )
        })
}

/// A parameter as a call sees it: what a named argument calls it, and
/// whether it soaks up the arguments after it.
#[derive(Clone, Debug)]
struct Shape {
    name: String,
    is_params: bool,
    optional: bool,
}

fn shapes_of(semantic: &Semantic, method: SymbolId) -> Vec<Shape> {
    let symbols = semantic.compilation.symbols();
    symbols
        .get(method)
        .as_method()
        .map(|detail| {
            detail
                .parameters
                .iter()
                .map(|&parameter| {
                    let found = symbols.get(parameter);
                    let detail = found.as_parameter();
                    Shape {
                        name: found.name.clone(),
                        is_params: detail.is_some_and(|detail| detail.is_params),
                        optional: detail.is_some_and(|detail| detail.has_default),
                    }
                })
                .collect()
        })
        .unwrap_or_default()
}

/// A call being rewritten, as a new parameter's value is worked out for
/// it: the text of the argument each old parameter was passed, when it was
/// passed one, and what the method was called on.
pub(super) struct CallSite {
    pub arguments: Vec<Option<String>>,
    /// `list` of `list.Add(x)`; `None` for an unqualified call, `new`, or
    /// an extension called on its receiver (which is its first argument).
    pub receiver: Option<String>,
}

/// Works out a new parameter's value at one call.
pub(super) type Compute<'c> = &'c dyn Fn(&CallSite) -> Option<String>;

/// Works out every edit of a change of signature.
pub(super) fn change(
    context: &mut Context<'_, '_>,
    target: &Target,
    order: &[ChangeParam],
) -> Result<WorkspaceEdit, String> {
    change_with(context, target, order, None)
}

/// [`change`], with the value of each new parameter that has no call-site
/// value of its own worked out for each call by `compute`.
pub(super) fn change_with(
    context: &mut Context<'_, '_>,
    target: &Target,
    order: &[ChangeParam],
    compute: Option<Compute<'_>>,
) -> Result<WorkspaceEdit, String> {
    let semantic = context.view.project();
    let shapes = shapes_of(semantic, target.symbol);
    let is_extension = semantic
        .compilation
        .symbols()
        .get(target.symbol)
        .as_method()
        .is_some_and(|method| method.is_extension);
    validate(&shapes, order, is_extension)?;

    let (_, references) = semantic
        .references_detailed(&context.path, target.name_offset, Some(&context.text))
        .ok_or_else(|| "Nothing refers to the member.".to_string())?;

    let family = semantic.cascade(target.symbol);
    let mut edit = WorkspaceEdit::default();
    let mut texts: HashMap<PathBuf, String> = HashMap::new();
    for reference in &references {
        let Some(token) = token_at(context, &reference.path, reference.span) else {
            // A `cref` in a comment names the member, not its parameters.
            continue;
        };
        if !texts.contains_key(&reference.path) {
            let Some(text) = text_of(context, &reference.path) else {
                continue;
            };
            texts.insert(reference.path.clone(), text);
        }
        let text = texts[&reference.path].clone();
        if reference.kind == ReferenceKind::Definition {
            let declaration = token.parent().clone();
            if !matches!(
                declaration.kind(),
                SyntaxKind::MethodDeclaration | SyntaxKind::ConstructorDeclaration
            ) {
                continue;
            }
            let edits = rewrite_declaration(&declaration, &text, order)?;
            edit.add_all(reference.path.clone(), edits);
            continue;
        }
        let Some((list, reduced)) = call_arguments(context, &reference.path, &token) else {
            continue;
        };
        // The overload the call bound to names its parameters.
        let called = with_view(context, &reference.path, |view| view.resolve(&token))
            .flatten()
            .and_then(|resolved| match resolved {
                crate::semantic::Resolved::Symbol(symbol) => Some(symbol),
                crate::semantic::Resolved::Local { .. } => None,
            })
            .filter(|symbol| semantic.compilation.symbols().get(*symbol).kind == SymbolKind::Method)
            .unwrap_or(target.symbol);
        // A named argument uses the names of the most derived override the
        // call can see, which need not be the member it bound to: try that
        // one's names, then those of the rest of the family.
        let receiver = if reduced { None } else { receiver_of(&token) };
        let call = compute.map(|compute| (compute, receiver));
        let mut result = rewrite_arguments(
            &list,
            &text,
            &shapes_of(semantic, called),
            order,
            reduced,
            call.as_ref(),
        );
        for &member in &family {
            if result.is_ok() {
                break;
            }
            result = rewrite_arguments(
                &list,
                &text,
                &shapes_of(semantic, member),
                order,
                reduced,
                call.as_ref(),
            );
        }
        if let Some(one) = result? {
            edit.add(reference.path.clone(), one);
        }
    }

    // `: base(...)` and `: this(...)` name no constructor.
    let is_constructor = semantic
        .compilation
        .symbols()
        .get(target.symbol)
        .as_method()
        .is_some_and(|method| method.method_kind == MethodKind::Constructor);
    if is_constructor {
        for (path, text, root) in project_files(context) {
            let initializers: Vec<SyntaxNode> = root
                .descendants()
                .filter(|node| {
                    matches!(
                        node.kind(),
                        SyntaxKind::BaseConstructorInitializer
                            | SyntaxKind::ThisConstructorInitializer
                    )
                })
                .collect();
            for initializer in initializers {
                let calls = with_view(context, &path, |view| {
                    view.bound_body(&initializer).is_some_and(|body| {
                        body.statements.iter().any(|statement| {
                            statement.span == initializer.span()
                                && matches!(
                                    &statement.kind,
                                    BoundStatementKind::ConstructorInitializer {
                                        constructor: Some(called),
                                        ..
                                    } if *called == target.symbol
                                )
                        })
                    })
                })
                .unwrap_or(false);
                if !calls {
                    continue;
                }
                let Some(list) = initializer.child_of_kind(SyntaxKind::ArgumentList) else {
                    continue;
                };
                let call = compute.map(|compute| (compute, None));
                if let Some(one) =
                    rewrite_arguments(&list, &text, &shapes, order, false, call.as_ref())?
                {
                    edit.add(path.clone(), one);
                }
            }
        }
    }
    if edit.is_empty() {
        return Err("The signature is already that.".to_string());
    }
    Ok(edit)
}

fn validate(shapes: &[Shape], order: &[ChangeParam], is_extension: bool) -> Result<(), String> {
    let mut seen = std::collections::HashSet::new();
    let mut names = std::collections::HashSet::new();
    for entry in order {
        match entry {
            ChangeParam::Existing(index) => {
                let Some(shape) = shapes.get(*index) else {
                    return Err(format!("There is no parameter {index}."));
                };
                if !seen.insert(*index) {
                    return Err(format!("'{}' is in the list twice.", shape.name));
                }
                names.insert(shape.name.clone());
            }
            ChangeParam::Added(added) => {
                if !is_identifier(&added.name) {
                    return Err(format!("'{}' is not a valid parameter name.", added.name));
                }
                if added.ty.trim().is_empty() {
                    return Err(format!("'{}' needs a type.", added.name));
                }
                if !names.insert(added.name.clone()) {
                    return Err(format!("There is already a parameter '{}'.", added.name));
                }
            }
        }
    }
    // A removed parameter's name is free for a new one, but only if
    // nothing else uses it; a clash between a kept name and a new one was
    // caught above.
    if is_extension && order.first() != Some(&ChangeParam::Existing(0)) {
        return Err("The 'this' parameter of an extension method has to stay first.".to_string());
    }
    let mut optional_seen = false;
    for (position, entry) in order.iter().enumerate() {
        let (is_params, optional) = match entry {
            ChangeParam::Existing(index) => (shapes[*index].is_params, shapes[*index].optional),
            ChangeParam::Added(added) => (false, added.default.is_some()),
        };
        if is_params && position + 1 != order.len() {
            return Err("A 'params' parameter has to be last.".to_string());
        }
        if optional {
            optional_seen = true;
        } else if optional_seen && !is_params {
            return Err("A required parameter cannot follow an optional one.".to_string());
        }
    }
    Ok(())
}

/// The argument list of the call `token` names, and whether it is an
/// extension method called on its receiver, which is then its first
/// argument.
pub(super) fn call_arguments(
    context: &mut Context<'_, '_>,
    path: &Path,
    token: &SyntaxToken,
) -> Option<(SyntaxNode, bool)> {
    // `new(…)`, `: base(…)` and `: this(…)` call a constructor by keyword.
    if matches!(
        token.kind(),
        SyntaxKind::NewKeyword | SyntaxKind::BaseKeyword | SyntaxKind::ThisKeyword
    ) && matches!(
        token.parent().kind(),
        SyntaxKind::ImplicitObjectCreationExpression
            | SyntaxKind::BaseConstructorInitializer
            | SyntaxKind::ThisConstructorInitializer
    ) {
        let creation = token.parent().clone();
        return Some((creation.child_of_kind(SyntaxKind::ArgumentList)?, false));
    }
    let mut node = token.parent().clone();
    while let Some(parent) = node.parent().cloned() {
        let is_name_of = matches!(
            parent.kind(),
            SyntaxKind::SimpleMemberAccessExpression
                | SyntaxKind::MemberBindingExpression
                | SyntaxKind::QualifiedName
                | SyntaxKind::AliasQualifiedName
        ) && parent.children().last().as_ref() == Some(&node);
        if !is_name_of {
            break;
        }
        node = parent;
    }
    let parent = node.parent()?.clone();
    match parent.kind() {
        SyntaxKind::InvocationExpression if parent.children().next().as_ref() == Some(&node) => {
            let list = parent.child_of_kind(SyntaxKind::ArgumentList)?;
            let reduced = is_reduced_call(context, path, &node);
            Some((list, reduced))
        }
        SyntaxKind::ObjectCreationExpression => {
            Some((parent.child_of_kind(SyntaxKind::ArgumentList)?, false))
        }
        SyntaxKind::Attribute => Some((
            parent.child_of_kind(SyntaxKind::AttributeArgumentList)?,
            false,
        )),
        _ => None,
    }
}

/// What the call whose name is `token` is called on: `a.b` of `a.b.M()`.
pub(super) fn receiver_of(token: &SyntaxToken) -> Option<String> {
    let name = token.parent();
    let parent = name.parent()?;
    (parent.kind() == SyntaxKind::SimpleMemberAccessExpression
        && parent.children().last().as_ref() == Some(name))
    .then(|| parent.children().next().map(|receiver| receiver.text()))
    .flatten()
}

/// Whether `callee`, the called part of a call of an extension method, is
/// `x.M` — the receiver passed as the `this` argument — rather than
/// `Extensions.M`.
pub(super) fn is_reduced_call(
    context: &mut Context<'_, '_>,
    path: &Path,
    callee: &SyntaxNode,
) -> bool {
    let Some(name) = rightmost_name(callee) else {
        return false;
    };
    let resolved = with_view(context, path, |view| view.resolve(&name)).flatten();
    let semantic = context.view.project();
    let Some(crate::semantic::Resolved::Symbol(method)) = resolved else {
        return false;
    };
    let symbols = semantic.compilation.symbols();
    if !symbols
        .get(method)
        .as_method()
        .is_some_and(|detail| detail.is_extension)
    {
        return false;
    }
    match callee.kind() {
        SyntaxKind::MemberBindingExpression => true,
        SyntaxKind::SimpleMemberAccessExpression => {
            let Some(receiver) = callee.children().next() else {
                return false;
            };
            // `Extensions.M(x)` names the type; anything else is a value.
            let Some(last) = rightmost_name(&receiver) else {
                return true;
            };
            let resolved = with_view(context, path, |view| view.resolve(&last)).flatten();
            !matches!(
                resolved,
                Some(crate::semantic::Resolved::Symbol(symbol))
                    if symbols.get(symbol).kind == SymbolKind::NamedType
            )
        }
        _ => false,
    }
}

/// The argument of a call, with the parameter it is for.
struct Passed {
    node: SyntaxNode,
    named: bool,
}

/// The edit that rewrites the arguments in `list` for the new order. `None`
/// when nothing about them changes.
fn rewrite_arguments(
    list: &SyntaxNode,
    text: &str,
    shapes: &[Shape],
    order: &[ChangeParam],
    reduced: bool,
    compute: Option<&(Compute<'_>, Option<String>)>,
) -> Result<Option<TextEdit>, String> {
    let argument_kind = if list.kind() == SyntaxKind::AttributeArgumentList {
        SyntaxKind::AttributeArgument
    } else {
        SyntaxKind::Argument
    };
    let arguments: Vec<SyntaxNode> = list
        .children()
        .filter(|child| child.kind() == argument_kind)
        .collect();
    // An attribute's `Name = value` sets a property, and stays at the end.
    let (arguments, properties): (Vec<SyntaxNode>, Vec<SyntaxNode>) = arguments
        .into_iter()
        .partition(|argument| argument.child_of_kind(SyntaxKind::NameEquals).is_none());
    let offset = usize::from(reduced);
    let mut passed: Vec<Vec<Passed>> = (0..shapes.len()).map(|_| Vec::new()).collect();
    let mut position = offset;
    for argument in &arguments {
        let named = argument
            .child_of_kind(SyntaxKind::NameColon)
            .and_then(|colon| colon.child_token_of_kind(SyntaxKind::IdentifierToken))
            .map(|token| token.value_text().to_string());
        let index = match &named {
            Some(name) => shapes
                .iter()
                .position(|shape| shape.name == *name)
                .ok_or_else(|| format!("A call passes '{name}', which is not a parameter."))?,
            None => {
                let index = position.min(shapes.len().saturating_sub(1));
                if position >= shapes.len() && !shapes.last().is_some_and(|shape| shape.is_params) {
                    return Err(
                        "A call passes more arguments than there are parameters.".to_string()
                    );
                }
                position += 1;
                index
            }
        };
        passed[index].push(Passed {
            node: argument.clone(),
            named: named.is_some(),
        });
    }

    let mut written: Vec<String> = Vec::new();
    let mut left_out = false;
    for (new_index, entry) in order.iter().enumerate() {
        if reduced && new_index == 0 {
            continue;
        }
        match entry {
            ChangeParam::Existing(index) => {
                let found = &passed[*index];
                if found.is_empty() {
                    left_out = true;
                    continue;
                }
                if left_out && found.len() > 1 {
                    return Err(format!(
                        "A call passes several arguments to '{}' after one it leaves out.",
                        shapes[*index].name
                    ));
                }
                for one in found {
                    let written_text = one.node.text();
                    if left_out && !one.named {
                        written.push(format!("{}: {written_text}", shapes[*index].name));
                    } else {
                        written.push(written_text);
                    }
                }
            }
            ChangeParam::Added(added) => {
                let value = match (&added.call_site, &added.default) {
                    (Some(value), _) if !value.trim().is_empty() => value.trim().to_string(),
                    (None, None) if compute.is_some() => {
                        let (compute, receiver) = compute.expect("checked");
                        let arguments = passed
                            .iter()
                            .map(|found| match found.as_slice() {
                                [one] => one
                                    .node
                                    .children()
                                    .filter(|child| child.kind() != SyntaxKind::NameColon)
                                    .last()
                                    .map(|value| value.text()),
                                _ => None,
                            })
                            .collect();
                        compute(&CallSite {
                            arguments,
                            receiver: receiver.clone(),
                        })
                        .ok_or_else(|| {
                            "A call does not pass what the new parameter needs.".to_string()
                        })?
                    }
                    (_, Some(_)) => {
                        left_out = true;
                        continue;
                    }
                    _ => "default".to_string(),
                };
                if left_out {
                    written.push(format!("{}: {value}", added.name));
                } else {
                    written.push(value);
                }
            }
        }
    }
    written.extend(properties.iter().map(SyntaxNode::text));

    let original: Vec<SyntaxNode> = list
        .children()
        .filter(|child| child.kind() == argument_kind)
        .collect();
    let separator = match original.as_slice() {
        [first, second, ..] => {
            text[first.span().end() as usize..second.span().start() as usize].to_string()
        }
        _ => ", ".to_string(),
    };
    let replaced = match (original.first(), original.last()) {
        (Some(first), Some(last)) => TextSpan::from_bounds(first.span().start(), last.span().end()),
        _ => {
            let open = list.first_token().ok_or("An argument list without '('.")?;
            TextSpan::new(open.span().end(), 0)
        }
    };
    let new_text = written.join(&separator);
    if new_text == text[replaced.start() as usize..replaced.end() as usize] {
        return Ok(None);
    }
    Ok(Some(TextEdit::new(replaced, new_text)))
}

/// The edits to one declaration: its parameter list, and its `<param>`
/// documentation.
pub(super) fn rewrite_declaration(
    declaration: &SyntaxNode,
    text: &str,
    order: &[ChangeParam],
) -> Result<Vec<TextEdit>, String> {
    let list = declaration
        .child_of_kind(SyntaxKind::ParameterList)
        .ok_or("A declaration without parameters.")?;
    let parameters: Vec<SyntaxNode> = list
        .children()
        .filter(|child| child.kind() == SyntaxKind::Parameter)
        .collect();
    let mut written = Vec::new();
    for entry in order {
        match entry {
            ChangeParam::Existing(index) => {
                let parameter = parameters
                    .get(*index)
                    .ok_or_else(|| format!("There is no parameter {index}."))?;
                written.push(parameter.text());
            }
            ChangeParam::Added(added) => written.push(match &added.default {
                Some(value) => format!("{} {} = {}", added.ty.trim(), added.name, value.trim()),
                None => format!("{} {}", added.ty.trim(), added.name),
            }),
        }
    }
    let separator = match parameters.as_slice() {
        [first, second, ..] => {
            text[first.span().end() as usize..second.span().start() as usize].to_string()
        }
        _ => ", ".to_string(),
    };
    let replaced = match (parameters.first(), parameters.last()) {
        (Some(first), Some(last)) => TextSpan::from_bounds(first.span().start(), last.span().end()),
        _ => {
            let open = list.first_token().ok_or("A parameter list without '('.")?;
            TextSpan::new(open.span().end(), 0)
        }
    };
    let mut edits = Vec::new();
    let new_text = written.join(&separator);
    if new_text != text[replaced.start() as usize..replaced.end() as usize] {
        edits.push(TextEdit::new(replaced, new_text));
    }
    let names: Vec<String> = parameters
        .iter()
        .map(|parameter| {
            parameter
                .child_token_of_kind(SyntaxKind::IdentifierToken)
                .map(|token| token.value_text().to_string())
                .unwrap_or_default()
        })
        .collect();
    if let Some(documentation) = reorder_documentation(declaration, text, &names, order) {
        edits.push(documentation);
    }
    Ok(edits)
}

/// The documentation comment's `<param>` elements in the new order: removed
/// parameters' gone, new ones' added empty. Only when the elements are one
/// run of whole lines, as they are when written by hand or by the editor.
fn reorder_documentation(
    declaration: &SyntaxNode,
    text: &str,
    names: &[String],
    order: &[ChangeParam],
) -> Option<TextEdit> {
    let first = declaration.first_token()?;
    // Each `///` line may be a trivia of its own: the comment is all of
    // them.
    let comments: Vec<TextSpan> = first
        .leading_trivia()
        .into_iter()
        .filter(|trivia| trivia.kind() == SyntaxKind::SingleLineDocumentationCommentTrivia)
        .map(|trivia| trivia.span())
        .collect();
    let span = TextSpan::from_bounds(comments.first()?.start(), comments.last()?.end());
    let start = line_start(text, span.start());
    let region = &text[start as usize..span.end() as usize];
    // The comment's lines, each with its line break.
    let mut lines: Vec<(u32, &str)> = Vec::new();
    let mut at = start;
    for line in region.split_inclusive('\n') {
        lines.push((at, line));
        at += line.len() as u32;
    }
    // Each `<param>` element: the lines it covers.
    let mut elements: Vec<(String, usize, usize)> = Vec::new();
    let mut index = 0;
    while index < lines.len() {
        let line = lines[index].1;
        if let Some(name) = param_name(line) {
            let mut end = index;
            while !lines[end].1.contains("</param>") && !lines[end].1.contains("/>") {
                end += 1;
                if end == lines.len() {
                    return None;
                }
            }
            elements.push((name, index, end));
            index = end + 1;
        } else {
            index += 1;
        }
    }
    if elements.is_empty() {
        return None;
    }
    let first_line = elements[0].1;
    let last_line = elements[elements.len() - 1].2;
    if elements.windows(2).any(|pair| pair[0].2 + 1 != pair[1].1) {
        return None;
    }
    let prefix: String = {
        let line = lines[first_line].1;
        let at = line.find("<param")?;
        line[..at].to_string()
    };
    let nl = newline(text);
    let mut out = String::new();
    for entry in order {
        match entry {
            ChangeParam::Existing(index) => {
                let name = names.get(*index)?;
                if let Some((_, from, to)) = elements.iter().find(|(element, _, _)| element == name)
                {
                    for line in &lines[*from..=*to] {
                        out.push_str(line.1);
                    }
                }
            }
            ChangeParam::Added(added) => {
                out.push_str(&format!(
                    "{prefix}<param name=\"{}\"></param>{nl}",
                    added.name
                ));
            }
        }
    }
    let from = lines[first_line].0;
    let to = lines[last_line].0 + lines[last_line].1.len() as u32;
    // The last line of the comment has no line break of its own in the
    // trivia; keep the text's.
    let replaced = &text[from as usize..to as usize];
    let out = if replaced.ends_with('\n') {
        out
    } else {
        out.trim_end_matches(['\r', '\n']).to_string()
    };
    (out != replaced).then(|| TextEdit::new(TextSpan::from_bounds(from, to), out))
}

/// The parameter a documentation line's `<param name="x">` opens, if it
/// opens one.
fn param_name(line: &str) -> Option<String> {
    let at = line.find("<param ")?;
    let rest = &line[at..];
    let name = rest.find("name=")? + 5;
    let quote = rest[name..].chars().next()?;
    let value = &rest[name + 1..];
    let end = value.find(quote)?;
    Some(value[..end].to_string())
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::{AddedParameter, ChangeParam};
    use crate::semantic::tests::compile;

    /// Every file after changing the signature at `marker` of the first.
    fn changed(
        files: &[(&str, &str)],
        marker: &str,
        order: &[ChangeParam],
    ) -> Vec<(String, String)> {
        let semantic = compile(files, false).expect("compiles");
        let offset = files[0].1.find(marker).expect("the marker") as u32;
        let edit = semantic
            .change_signature(
                &PathBuf::from(format!("/p/{}", files[0].0)),
                offset,
                None,
                order,
            )
            .expect("the change");
        files
            .iter()
            .map(|(name, text)| {
                let path = PathBuf::from(format!("/p/{name}"));
                (
                    (*name).to_string(),
                    crate::edit::apply(text, edit.edits_of(&path)),
                )
            })
            .collect()
    }

    fn refused(files: &[(&str, &str)], marker: &str, order: &[ChangeParam]) -> String {
        let semantic = compile(files, false).expect("compiles");
        let offset = files[0].1.find(marker).expect("the marker") as u32;
        semantic
            .change_signature(
                &PathBuf::from(format!("/p/{}", files[0].0)),
                offset,
                None,
                order,
            )
            .expect_err("refused")
    }

    use ChangeParam::Existing;

    #[test]
    fn reordering_moves_the_parameters_and_every_argument() {
        let shop = "public class Shop\n{\n    /// <summary>Buys.</summary>\n    /// <param name=\"item\">What.</param>\n    /// <param name=\"count\">How many.</param>\n    /// <param name=\"gift\">Wrapped.</param>\n    public void Buy(string item, int count, bool gift = false)\n    {\n    }\n}\n";
        let customer = "public class Customer\n{\n    public void Visit(Shop shop)\n    {\n        shop.Buy(\"apple\", 3);\n        shop.Buy(\"pear\", 1, true);\n        shop.Buy(count: 2, item: \"fig\");\n    }\n}\n";
        let after = changed(
            &[("Shop.cs", shop), ("Customer.cs", customer)],
            "Buy(",
            &[Existing(1), Existing(0), Existing(2)],
        );
        assert_eq!(
            after[0].1,
            "public class Shop\n{\n    /// <summary>Buys.</summary>\n    /// <param name=\"count\">How many.</param>\n    /// <param name=\"item\">What.</param>\n    /// <param name=\"gift\">Wrapped.</param>\n    public void Buy(int count, string item, bool gift = false)\n    {\n    }\n}\n"
        );
        assert_eq!(
            after[1].1,
            "public class Customer\n{\n    public void Visit(Shop shop)\n    {\n        shop.Buy(3, \"apple\");\n        shop.Buy(1, \"pear\", true);\n        shop.Buy(count: 2, item: \"fig\");\n    }\n}\n"
        );
    }

    #[test]
    fn removing_and_adding_parameters_updates_calls() {
        let text = "class Logger\n{\n    public void Log(string message, int level)\n    {\n    }\n\n    void Use()\n    {\n        Log(\"a\", 1);\n        this.Log(\"b\", level: 2);\n    }\n}\n";
        let after = changed(
            &[("A.cs", text)],
            "Log(string",
            &[
                Existing(0),
                ChangeParam::Added(AddedParameter {
                    ty: "bool".into(),
                    name: "urgent".into(),
                    default: None,
                    call_site: Some("false".into()),
                }),
            ],
        );
        assert_eq!(
            after[0].1,
            "class Logger\n{\n    public void Log(string message, bool urgent)\n    {\n    }\n\n    void Use()\n    {\n        Log(\"a\", false);\n        this.Log(\"b\", false);\n    }\n}\n"
        );
    }

    #[test]
    fn a_left_out_argument_names_the_ones_after_it() {
        let text = "class C\n{\n    void M(int a, int b = 2, int c = 3) { }\n    void Use() { M(1, c: 5); M(1); }\n}\n";
        let after = changed(
            &[("A.cs", text)],
            "M(int",
            &[
                Existing(0),
                ChangeParam::Added(AddedParameter {
                    ty: "string".into(),
                    name: "tag".into(),
                    default: Some("null".into()),
                    call_site: None,
                }),
                Existing(2),
                Existing(1),
            ],
        );
        assert_eq!(
            after[0].1,
            "class C\n{\n    void M(int a, string tag = null, int c = 3, int b = 2) { }\n    void Use() { M(1, c: 5); M(1); }\n}\n"
        );
    }

    #[test]
    fn overrides_implementations_and_interfaces_change_together() {
        let text = "interface IShape { double Scale(double x, double y); }\n\
                    abstract class Shape : IShape { public abstract double Scale(double x, double y); }\n\
                    class Box : Shape { public override double Scale(double w, double h) => w * h; }\n\
                    class User { double Use(IShape s, Box b) => s.Scale(1, 2) + b.Scale(3, h: 4); }\n";
        let after = changed(
            &[("A.cs", text)],
            "Scale(double x",
            &[Existing(1), Existing(0)],
        );
        assert_eq!(
            after[0].1,
            "interface IShape { double Scale(double y, double x); }\n\
             abstract class Shape : IShape { public abstract double Scale(double y, double x); }\n\
             class Box : Shape { public override double Scale(double h, double w) => w * h; }\n\
             class User { double Use(IShape s, Box b) => s.Scale(2, 1) + b.Scale(h: 4, 3); }\n"
        );
    }

    #[test]
    fn constructors_change_with_new_and_base_calls() {
        let text = "class Animal\n{\n    public Animal(string name, int legs) { }\n}\n\
                    class Dog : Animal\n{\n    public Dog() : base(\"dog\", 4) { }\n}\n\
                    class Zoo\n{\n    Animal a = new Animal(\"cat\", 4);\n    Animal b = new(\"bird\", 2);\n}\n";
        let after = changed(
            &[("A.cs", text)],
            "Animal(string",
            &[Existing(1), Existing(0)],
        );
        assert_eq!(
            after[0].1,
            "class Animal\n{\n    public Animal(int legs, string name) { }\n}\n\
             class Dog : Animal\n{\n    public Dog() : base(4, \"dog\") { }\n}\n\
             class Zoo\n{\n    Animal a = new Animal(4, \"cat\");\n    Animal b = new(2, \"bird\");\n}\n"
        );
    }

    #[test]
    fn an_extension_keeps_its_receiver_first() {
        let text = "static class Text\n{\n    public static string Pad(this string s, int left, int right) => s;\n}\n\
                    class Use\n{\n    string M(string v) => v.Pad(1, 2) + Text.Pad(v, 3, 4);\n}\n";
        let after = changed(
            &[("A.cs", text)],
            "Pad(this",
            &[Existing(0), Existing(2), Existing(1)],
        );
        assert_eq!(
            after[0].1,
            "static class Text\n{\n    public static string Pad(this string s, int right, int left) => s;\n}\n\
             class Use\n{\n    string M(string v) => v.Pad(2, 1) + Text.Pad(v, 4, 3);\n}\n"
        );
        assert!(
            refused(
                &[("A.cs", text)],
                "Pad(this",
                &[Existing(1), Existing(0), Existing(2)]
            )
            .contains("'this'")
        );
    }

    #[test]
    fn params_stay_last_and_together() {
        let text = "class C\n{\n    void Sum(string label, params int[] values) { }\n    void Use() { Sum(\"a\", 1, 2, 3); }\n}\n";
        assert!(
            refused(&[("A.cs", text)], "Sum(string", &[Existing(1), Existing(0)])
                .contains("params")
        );
        let after = changed(
            &[("A.cs", text)],
            "Sum(string",
            &[
                Existing(0),
                ChangeParam::Added(AddedParameter {
                    ty: "int".into(),
                    name: "scale".into(),
                    default: None,
                    call_site: Some("10".into()),
                }),
                Existing(1),
            ],
        );
        assert_eq!(
            after[0].1,
            "class C\n{\n    void Sum(string label, int scale, params int[] values) { }\n    void Use() { Sum(\"a\", 10, 1, 2, 3); }\n}\n"
        );
    }

    #[test]
    fn the_dialog_is_told_the_parameters() {
        let text = "class C\n{\n    public void M(ref int a, string b = \"x\") { }\n}\n";
        let semantic = compile(&[("A.cs", text)], false).expect("compiles");
        let info = semantic
            .change_signature_info(
                &PathBuf::from("/p/A.cs"),
                text.find("M(").unwrap() as u32,
                None,
            )
            .expect("info");
        assert_eq!(info.display, "C.M(ref int a, string b)");
        assert_eq!(info.parameters[1].default.as_deref(), Some("\"x\""));
        assert!(!info.first_is_fixed);
    }
}
