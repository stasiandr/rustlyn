//! Extract method, extract local function: move the selected statements,
//! or the selected expression, into a new method and call it from where
//! they were.
//!
//! Roslyn's `ExtractMethod`. What the new method takes and gives back comes
//! from following every name in the selection to what it binds to:
//!
//! * A local or parameter declared outside and read inside is passed in.
//! * One written inside and read after the selection comes back out: as the
//!   return value when it is the only one, through `ref` (or `out`, when the
//!   selection assigns it before reading it) otherwise.
//! * One declared inside and used after is returned and declared at the
//!   call; two of those cannot both come back, and nothing is offered.
//! * No `this` and no instance member makes the method `static`; an `await`
//!   makes it `async` and returns a `Task`; a type parameter of the method
//!   makes it generic.
//!
//! Control flow that would leave the selection — `break` or `continue` to a
//! loop outside it, `goto`, `yield` — cannot be moved, and a `return` can
//! only when the selection runs to the end of the method, where the call
//! can return what the new method does.
//!
//! "After the selection" is the text after it, and inside a loop, anything
//! in the loop: the next time round reads what this time wrote.

use std::collections::HashSet;

use rustlyn_semantics::{MethodKind, Modifiers, SymbolId, SymbolKind, Type};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::super::text::{
    enclosing_member, fresh_name, is_only_written, is_statement, is_type_declaration, is_written,
    parenthesized_for, reindent, skip_parentheses, statements_of,
};
use super::super::{ActionKind, CodeAction, Context};
use crate::edit::TextEdit;
use crate::semantic::Resolved;

pub(super) fn offer(context: &mut Context<'_, '_>, found: &mut Vec<CodeAction>) {
    let Some(selection) = select(context) else {
        return;
    };
    let Some(plan) = analyze(context, &selection) else {
        return;
    };
    if let Some(edits) = write(context, &selection, &plan, Target::Method) {
        found.push(context.local("Extract method", ActionKind::Extract, None, edits));
    }
    if let Some(edits) = write(context, &selection, &plan, Target::LocalFunction) {
        found.push(context.local("Extract local function", ActionKind::Extract, None, edits));
    }
}

/// What is being extracted.
enum Selection {
    /// Consecutive statements of one block.
    Statements(Vec<SyntaxNode>),
    /// One expression with a value.
    Expression(SyntaxNode),
}

impl Selection {
    fn span(&self) -> TextSpan {
        match self {
            Self::Statements(statements) => TextSpan::from_bounds(
                statements[0].span().start(),
                statements[statements.len() - 1].span().end(),
            ),
            Self::Expression(node) => node.span(),
        }
    }

    fn first(&self) -> &SyntaxNode {
        match self {
            Self::Statements(statements) => &statements[0],
            Self::Expression(node) => node,
        }
    }
}

/// Where the new code goes.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Target {
    /// A private method after the member the selection is in.
    Method,
    /// A local function at the end of the member's body.
    LocalFunction,
}

/// The selection as whole statements or one whole expression, or nothing.
fn select(context: &mut Context<'_, '_>) -> Option<Selection> {
    let span = context.trimmed_span();
    if span.is_empty() {
        return None;
    }
    let root = context.view.syntax_root();
    let covering = root.find_node(span)?;
    // One statement, or an expression that is a whole statement's.
    if is_statement(covering.kind()) && covering.span() == span {
        let statement = covering.clone();
        let parent = statement.parent()?;
        if !matches!(parent.kind(), SyntaxKind::Block | SyntaxKind::SwitchSection) {
            return None;
        }
        return Some(Selection::Statements(vec![statement]));
    }
    if matches!(
        covering.kind(),
        SyntaxKind::Block | SyntaxKind::SwitchSection
    ) {
        let inside: Vec<SyntaxNode> = statements_of(&covering)
            .into_iter()
            .filter(|statement| span.contains_span(statement.span()))
            .collect();
        let first = inside.first()?;
        let last = inside.last()?;
        if first.span().start() != span.start() || last.span().end() != span.end() {
            return None;
        }
        return Some(Selection::Statements(inside));
    }
    if covering.span() != span || !covering.kind().is_expression() {
        return None;
    }
    if !super::introduce_variable::is_value_expression(context, &covering)
        && !matches!(covering.kind(), SyntaxKind::InvocationExpression)
    {
        return None;
    }
    if covering
        .parent()
        .is_some_and(|parent| parent.kind() == SyntaxKind::ExpressionStatement)
    {
        return Some(Selection::Statements(vec![covering.parent()?.clone()]));
    }
    Some(Selection::Expression(covering))
}

/// A local or parameter the selection uses.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Variable {
    Local(TextSpan),
    Parameter(SymbolId),
}

/// How the selection uses one variable.
#[derive(Clone, Debug)]
struct Usage {
    variable: Variable,
    name: String,
    ty: Type,
    declared_inside: bool,
    read_inside: bool,
    written_inside: bool,
    /// The first use inside is `x = ...;`, a statement of the selection
    /// itself: it is assigned before anything could read it.
    assigned_first: Option<TextSpan>,
    used_after: bool,
    first_use: u32,
    /// Where it was declared: what orders the new method's parameters.
    declared: u32,
}

/// How a variable crosses into and out of the new method.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Flow {
    /// Passed by value.
    In,
    /// Declared inside the new method, and nowhere near the call.
    Local,
    /// Returned: assigned at the call.
    Returned,
    /// Declared inside the selection and returned: declared at the call.
    ReturnedDeclaration,
    Ref,
    Out,
}

/// Everything the new method needs.
struct Plan {
    member: SyntaxNode,
    flows: Vec<(Usage, Flow)>,
    is_static: bool,
    is_async: bool,
    /// The method's type parameters the selection uses, with their
    /// constraint clauses.
    type_parameters: Vec<(String, Option<String>)>,
    /// What the new method returns, written out.
    returns: String,
    /// `return NewMethod(...)`: the selection ended the method with a
    /// `return`.
    returns_through: bool,
    /// The selection calls a local function of the member: the new code
    /// has to stay where it can see it.
    uses_local_function: bool,
}

fn analyze(context: &mut Context<'_, '_>, selection: &Selection) -> Option<Plan> {
    let first = selection.first().clone();
    let member = enclosing_member(&first)?;
    if !matches!(
        member.kind(),
        SyntaxKind::MethodDeclaration
            | SyntaxKind::ConstructorDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::IndexerDeclaration
            | SyntaxKind::OperatorDeclaration
            | SyntaxKind::ConversionOperatorDeclaration
            | SyntaxKind::DestructorDeclaration
            | SyntaxKind::EventDeclaration
    ) {
        return None;
    }
    if first.ancestors().any(|ancestor| {
        matches!(
            ancestor.kind(),
            SyntaxKind::BaseConstructorInitializer
                | SyntaxKind::ThisConstructorInitializer
                | SyntaxKind::AttributeList
                | SyntaxKind::Parameter
        )
    }) {
        return None;
    }
    let span = selection.span();
    context.view.bound_body(&first)?;

    // Control flow that would leave the selection.
    let nodes: Vec<SyntaxNode> = match selection {
        Selection::Statements(statements) => statements.clone(),
        Selection::Expression(node) => vec![node.clone()],
    };
    let mut returns = Vec::new();
    let mut awaits = false;
    for node in &nodes {
        // A selected `return` statement is itself a way out.
        if node.kind() == SyntaxKind::ReturnStatement {
            returns.push(node.clone());
        }
        for inner in node.descendants() {
            if nested_function_between(&inner, node) {
                continue;
            }
            match inner.kind() {
                SyntaxKind::GotoStatement
                | SyntaxKind::GotoCaseStatement
                | SyntaxKind::GotoDefaultStatement
                | SyntaxKind::YieldReturnStatement
                | SyntaxKind::YieldBreakStatement
                | SyntaxKind::LabeledStatement => return None,
                SyntaxKind::BreakStatement | SyntaxKind::ContinueStatement => {
                    let target = inner.ancestors().find(|ancestor| {
                        matches!(
                            ancestor.kind(),
                            SyntaxKind::WhileStatement
                                | SyntaxKind::DoStatement
                                | SyntaxKind::ForStatement
                                | SyntaxKind::ForEachStatement
                                | SyntaxKind::ForEachVariableStatement
                        ) || (inner.kind() == SyntaxKind::BreakStatement
                            && ancestor.kind() == SyntaxKind::SwitchStatement)
                    });
                    if !target.is_some_and(|target| span.contains_span(target.span())) {
                        return None;
                    }
                }
                SyntaxKind::ReturnStatement => returns.push(inner.clone()),
                SyntaxKind::AwaitExpression => awaits = true,
                SyntaxKind::DeclarationExpression
                    if matches!(selection, Selection::Expression(_)) =>
                {
                    return None;
                }
                _ => {}
            }
        }
    }
    // A `return` inside a lambda or a local function returns from that, and
    // a method pulled out of it would have to return its type: not offered.
    if !returns.is_empty() && nested_function_between(&first, &member) {
        return None;
    }
    // A constructor may assign the type's readonly fields; the method it
    // would call instead may not.
    if member.kind() == SyntaxKind::ConstructorDeclaration
        && assigns_readonly_field(context, &nodes)
    {
        return None;
    }
    // `foreach await` and `using await` are awaits too.
    if nodes.iter().any(|node| {
        node.descendant_tokens()
            .any(|token| token.kind() == SyntaxKind::AwaitKeyword)
    }) {
        awaits = true;
    }

    // Functions the selection is inside, whose parameters it can read.
    let symbols = context.view.compiled().symbols();
    let functions: HashSet<SymbolId> = std::iter::once(first.clone())
        .chain(first.ancestors())
        .take_while(|ancestor| {
            ancestor.span().contains_span(member.span())
                || member.span().contains_span(ancestor.span())
        })
        .filter(|ancestor| {
            member.span().contains_span(ancestor.span())
                && matches!(
                    ancestor.kind(),
                    SyntaxKind::LocalFunctionStatement
                        | SyntaxKind::GetAccessorDeclaration
                        | SyntaxKind::SetAccessorDeclaration
                        | SyntaxKind::InitAccessorDeclaration
                        | SyntaxKind::AddAccessorDeclaration
                        | SyntaxKind::RemoveAccessorDeclaration
                )
                || ancestor == &member
        })
        .filter_map(|ancestor| context.view.declared(&ancestor))
        .collect();
    let member_symbol = context.view.declared(&member);
    let _ = symbols;

    // Loops around the selection: a write in one is read the next time
    // round by whatever in the loop reads it.
    let loops: Vec<SyntaxNode> = first
        .ancestors()
        .take_while(|ancestor| ancestor != &member)
        .filter(|ancestor| {
            matches!(
                ancestor.kind(),
                SyntaxKind::WhileStatement
                    | SyntaxKind::DoStatement
                    | SyntaxKind::ForStatement
                    | SyntaxKind::ForEachStatement
                    | SyntaxKind::ForEachVariableStatement
            )
        })
        .collect();

    let mut usages: Vec<Usage> = Vec::new();
    let mut uses_instance = false;
    let mut uses_local_function = false;
    let mut type_parameters: Vec<SymbolId> = Vec::new();
    let tokens: Vec<SyntaxToken> = member.descendant_tokens().collect();
    for token in &tokens {
        let inside = span.contains_span(token.span());
        if inside
            && matches!(
                token.kind(),
                SyntaxKind::ThisKeyword | SyntaxKind::BaseKeyword
            )
        {
            uses_instance = true;
            continue;
        }
        if token.kind() != SyntaxKind::IdentifierToken {
            continue;
        }
        let name_node = token.parent().clone();
        if name_node.kind() != SyntaxKind::IdentifierName
            && name_node.kind() != SyntaxKind::GenericName
        {
            continue;
        }
        if name_node.parent().is_some_and(|parent| {
            matches!(
                parent.kind(),
                SyntaxKind::NameColon | SyntaxKind::NameEquals
            )
        }) {
            continue;
        }
        let after = token.span().start() >= span.end()
            || (!inside
                && loops
                    .iter()
                    .any(|looped| looped.span().contains_span(token.span())));
        if !inside && !after {
            continue;
        }
        // A delegate local called by name binds the call to `Invoke`; what
        // the name reads is still the local.
        let bound_local = context.view.bound_body(&name_node).and_then(|body| {
            match body.reference_at(name_node.span()) {
                Some(rustlyn_semantics::BoundSymbol::Local(local)) => body
                    .locals
                    .get(local.0 as usize)
                    .map(|local| Resolved::Local {
                        tree: context.view.tree,
                        span: local.span,
                        name: local.name.clone(),
                        ty: local.ty.clone(),
                    }),
                Some(rustlyn_semantics::BoundSymbol::Declared(symbol))
                    if context.view.compiled().symbols().get(symbol).kind
                        == SymbolKind::Parameter =>
                {
                    Some(Resolved::Symbol(symbol))
                }
                _ => None,
            }
        });
        let Some(resolved) = bound_local.or_else(|| context.view.resolve(token)) else {
            if inside {
                // A name that does not bind: nothing can be said about it.
                return None;
            }
            continue;
        };
        let (variable, name, ty, declared_at) = match resolved {
            Resolved::Local {
                span: at, name, ty, ..
            } => (Variable::Local(at), name, ty, Some(at)),
            Resolved::Symbol(symbol) => {
                let symbols = context.view.compiled().symbols();
                let found = symbols.get(symbol);
                match found.kind {
                    SymbolKind::Parameter
                        if found
                            .container
                            .is_some_and(|container| functions.contains(&container)) =>
                    {
                        let at = found.locations.first().map(|location| location.span);
                        (
                            Variable::Parameter(symbol),
                            found.name.clone(),
                            context.view.symbol_type(symbol),
                            at,
                        )
                    }
                    SymbolKind::Parameter => {
                        // A parameter of a local function the selection
                        // declares, or of a lambda.
                        continue;
                    }
                    SymbolKind::TypeParameter => {
                        if inside
                            && found.container.is_some()
                            && found.container == member_symbol
                            && !type_parameters.contains(&symbol)
                        {
                            type_parameters.push(symbol);
                        }
                        continue;
                    }
                    SymbolKind::Method
                        if found.as_method().is_some_and(|method| {
                            method.method_kind == MethodKind::LocalFunction
                        }) =>
                    {
                        let declared_inside = found
                            .locations
                            .first()
                            .is_some_and(|location| span.contains_span(location.span));
                        if inside && !declared_inside {
                            uses_local_function = true;
                        }
                        if after && declared_inside {
                            return None;
                        }
                        continue;
                    }
                    SymbolKind::Field
                    | SymbolKind::Property
                    | SymbolKind::Method
                    | SymbolKind::Event => {
                        if inside
                            && !found.modifiers.contains(Modifiers::STATIC)
                            && !found.modifiers.contains(Modifiers::CONST)
                            && found.as_method().is_none_or(|method| {
                                matches!(
                                    method.method_kind,
                                    MethodKind::Ordinary
                                        | MethodKind::PropertyGet
                                        | MethodKind::PropertySet
                                )
                            })
                            && found.container.is_some_and(|container| {
                                symbols.get(container).kind == SymbolKind::NamedType
                            })
                            && is_implicit_this(&name_node)
                        {
                            uses_instance = true;
                        }
                        continue;
                    }
                    _ => continue,
                }
            }
        };
        let declared_inside = declared_at.is_some_and(|at| span.contains_span(at));
        let index = match usages.iter().position(|usage| usage.variable == variable) {
            Some(index) => index,
            None => {
                usages.push(Usage {
                    variable,
                    name,
                    ty,
                    declared_inside,
                    read_inside: false,
                    written_inside: false,
                    assigned_first: None,
                    used_after: false,
                    first_use: u32::MAX,
                    declared: declared_at.map_or(token.span().start(), |at| at.start()),
                });
                usages.len() - 1
            }
        };
        let usage = &mut usages[index];
        if inside {
            let only_written = is_only_written(&name_node);
            if usage.first_use == u32::MAX {
                usage.first_use = token.span().start();
                if only_written && is_top_level_assignment(&name_node, selection) {
                    usage.assigned_first = Some(token.span());
                }
            }
            if !only_written {
                usage.read_inside = true;
            }
            if is_written(&name_node) {
                usage.written_inside = true;
            }
        } else if after {
            usage.used_after = true;
        }
    }
    // Declared by the selection but only ever used after it: nothing to
    // do with the selection.
    // A declaration's own name is not a use; one declared inside and used
    // after is.
    usages
        .retain(|usage| usage.first_use != u32::MAX || (usage.declared_inside && usage.used_after));
    usages.sort_by_key(|usage| usage.declared);

    // Returns leave the member: only the member's own, at its very end.
    let mut returns_through = false;
    let mut member_returns = "void".to_string();
    if !returns.is_empty() {
        let Selection::Statements(statements) = selection else {
            return None;
        };
        let body = statements[0].parent()?;
        let last = statements.last()?;
        if body.kind() != SyntaxKind::Block
            || body.parent() != Some(&member)
            || statements_of(body).last() != Some(last)
            || member.kind() != SyntaxKind::MethodDeclaration
            || member
                .child_token_of_kind(SyntaxKind::AsyncKeyword)
                .is_some()
        {
            return None;
        }
        let declared = member
            .children()
            .find(|child| child.kind().is_type_node())?;
        member_returns = declared.text();
        if member_returns != "void" {
            if last.kind() != SyntaxKind::ReturnStatement
                && last.kind() != SyntaxKind::ThrowStatement
            {
                return None;
            }
            returns_through = true;
        }
    }

    // How each variable crosses.
    let mut flows = Vec::new();
    for usage in &usages {
        let output = usage.used_after && (usage.written_inside || usage.declared_inside);
        let flow = if usage.declared_inside {
            if !usage.used_after {
                continue;
            }
            // `int result;` with nothing assigned to it in the selection
            // would be returned unassigned (CS0165): the declaration has
            // to stay where the code after it assigns it.
            let uninitialized = member
                .find_token(usage.declared)
                .map(|token| token.parent().clone())
                .is_some_and(|declarator| {
                    declarator.kind() == SyntaxKind::VariableDeclarator
                        && declarator
                            .child_of_kind(SyntaxKind::EqualsValueClause)
                            .is_none()
                });
            if uninitialized && !usage.written_inside {
                return None;
            }
            Flow::ReturnedDeclaration
        } else if output {
            if usage.assigned_first.is_some() && !usage.read_inside_before_write() {
                Flow::Out
            } else {
                // Passed in, it is read at the call: a local nothing has
                // assigned yet cannot be (CS0165).
                if unassigned_before(&member, usage, selection.span()) {
                    return None;
                }
                Flow::Ref
            }
        } else if usage.written_inside && !usage.read_inside && usage.assigned_first.is_some() {
            Flow::Local
        } else {
            Flow::In
        };
        flows.push((usage.clone(), flow));
    }
    let outputs: Vec<usize> = flows
        .iter()
        .enumerate()
        .filter(|(_, (_, flow))| matches!(flow, Flow::Ref | Flow::Out | Flow::ReturnedDeclaration))
        .map(|(index, _)| index)
        .collect();
    let mut returns_text = match selection {
        Selection::Expression(node) => {
            let ty = context.view.expression_type(node)?;
            if matches!(ty, Type::Void | Type::Null) {
                return None;
            }
            if !outputs.is_empty() {
                return None;
            }
            context.view.display_type(&ty, node)?
        }
        Selection::Statements(_) => member_returns.clone(),
    };
    if let Selection::Statements(_) = selection {
        if outputs.len() == 1 && returns.is_empty() {
            let index = outputs[0];
            let (usage, flow) = &mut flows[index];
            returns_text = context.view.display_type(&usage.ty, &member)?;
            *flow = match flow {
                Flow::ReturnedDeclaration => Flow::ReturnedDeclaration,
                _ => Flow::Returned,
            };
        } else if outputs
            .iter()
            .any(|&index| flows[index].1 == Flow::ReturnedDeclaration)
            || (!returns.is_empty() && !outputs.is_empty())
        {
            return None;
        }
    }
    if awaits
        && flows
            .iter()
            .any(|(_, flow)| matches!(flow, Flow::Ref | Flow::Out))
    {
        return None;
    }
    if awaits {
        let task = if returns_text == "void" {
            "System.Threading.Tasks.Task"
        } else {
            "System.Threading.Tasks.Task`1"
        };
        let task = context.view.compiled().type_by_metadata_name(task)?;
        let task = if returns_text == "void" {
            Type::named(task)
        } else {
            // The type argument is written out below; any will do to find
            // how `Task` itself is spelled here.
            Type::named(task)
        };
        let written = context.view.display_type(&task, &member)?;
        returns_text = if returns_text == "void" {
            written
        } else {
            format!("{written}<{returns_text}>")
        };
    }

    let member_static = member
        .child_token_of_kind(SyntaxKind::StaticKeyword)
        .is_some();
    let clause_for = |name: &str| {
        member
            .children()
            .filter(|child| child.kind() == SyntaxKind::TypeParameterConstraintClause)
            .find(|clause| {
                clause
                    .descendant_tokens()
                    .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                    .is_some_and(|named| named.value_text() == name)
            })
            .map(|clause| clause.text())
    };
    let mut type_parameters: Vec<(String, Option<String>)> = type_parameters
        .iter()
        .map(|&symbol| {
            let name = context.view.compiled().symbols().get(symbol).name.clone();
            let clause = clause_for(&name);
            (name, clause)
        })
        .collect();
    // Types of what is passed that mention a type parameter the selection
    // does not name itself still need it declared.
    for (usage, _) in &flows {
        for symbol in type_parameters_in(&usage.ty) {
            let found = context.view.compiled().symbols().get(symbol);
            if found.container == member_symbol
                && !type_parameters.iter().any(|(name, _)| *name == found.name)
            {
                type_parameters.push((found.name.clone(), clause_for(&found.name)));
            }
        }
    }
    type_parameters.sort_by_key(|(name, _)| {
        member
            .child_of_kind(SyntaxKind::TypeParameterList)
            .and_then(|list| list.text().find(name.as_str()))
    });

    Some(Plan {
        member,
        flows,
        is_static: member_static || !uses_instance,
        is_async: awaits,
        type_parameters,
        returns: returns_text,
        returns_through,
        uses_local_function,
    })
}

/// Whether `usage` is a local declared without a value and not written
/// between its declaration and `start`: reading it there is CS0165.
fn unassigned_before(member: &SyntaxNode, usage: &Usage, selection: TextSpan) -> bool {
    let Some(declarator) = member
        .find_token(usage.declared)
        .map(|token| token.parent().clone())
        .filter(|declarator| declarator.kind() == SyntaxKind::VariableDeclarator)
    else {
        return false;
    };
    if declarator
        .child_of_kind(SyntaxKind::EqualsValueClause)
        .is_some()
    {
        return false;
    }
    !member.descendants().any(|name| {
        name.kind() == SyntaxKind::IdentifierName
            && name.span().start() > declarator.span().end()
            && name.span().end() <= selection.start()
            && name.text().trim() == usage.name
            && is_written(&name)
    })
}

impl Usage {
    /// Whether a read inside comes before the assignment that starts it.
    fn read_inside_before_write(&self) -> bool {
        self.assigned_first.is_none()
    }
}

/// Whether a name with nothing in front of it, or `this.` in front of it,
/// is a use of the instance: `Count`, `this.Count`, but not `other.Count`,
/// and not the `Count` of `new C { Count = 1 }`.
fn is_implicit_this(name: &SyntaxNode) -> bool {
    let Some(parent) = name.parent() else {
        return true;
    };
    match parent.kind() {
        SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::PointerMemberAccessExpression => {
            if parent.children().last().as_ref() != Some(name) {
                return true;
            }
            parent.children().next().is_some_and(|left| {
                matches!(
                    left.kind(),
                    SyntaxKind::ThisExpression | SyntaxKind::BaseExpression
                )
            })
        }
        SyntaxKind::MemberBindingExpression => false,
        SyntaxKind::SimpleAssignmentExpression => !parent.parent().is_some_and(|grand| {
            grand.kind() == SyntaxKind::ObjectInitializerExpression
                || grand.kind() == SyntaxKind::WithInitializerExpression
        }),
        _ => true,
    }
}

/// Whether `name` is the target of `x = ...;`, a statement the selection
/// holds directly.
fn is_top_level_assignment(name: &SyntaxNode, selection: &Selection) -> bool {
    let Selection::Statements(statements) = selection else {
        return false;
    };
    let Some(assignment) = name.parent() else {
        return false;
    };
    // `size = size + 1` reads `size` before it writes it.
    let text = name.text();
    let reads_itself = assignment.children().nth(1).is_some_and(|value| {
        value.descendants().any(|inner| {
            inner.kind() == SyntaxKind::IdentifierName && inner.text().trim() == text.trim()
        }) || (value.kind() == SyntaxKind::IdentifierName && value.text().trim() == text.trim())
    });
    assignment.kind() == SyntaxKind::SimpleAssignmentExpression
        && !reads_itself
        && assignment
            .parent()
            .is_some_and(|statement| statements.contains(statement))
}

/// Whether a lambda or local function sits between `inner` and `outer`:
/// its `return` and its `await` are its own.
/// Whether the code writes a `readonly` field: assigns it, increments it,
/// or passes it by `ref` or `out`.
fn assigns_readonly_field(context: &mut Context<'_, '_>, nodes: &[SyntaxNode]) -> bool {
    for node in nodes {
        let tokens: Vec<SyntaxToken> = node
            .descendant_tokens()
            .filter(|token| token.kind() == SyntaxKind::IdentifierToken)
            .collect();
        for token in tokens {
            if !is_written(token.parent()) {
                continue;
            }
            let Some(Resolved::Symbol(symbol)) = context.view.resolve(&token) else {
                continue;
            };
            let found = context.view.compiled().symbols().get(symbol);
            if found.kind == SymbolKind::Field && found.modifiers.contains(Modifiers::READONLY) {
                return true;
            }
            // A get-only auto-property is as readonly as its backing field.
            if found.as_property().is_some_and(|property| {
                !property.has_set && !property.has_init && property.setter.is_none()
            }) {
                return true;
            }
        }
    }
    false
}

fn nested_function_between(inner: &SyntaxNode, outer: &SyntaxNode) -> bool {
    inner
        .ancestors()
        .take_while(|ancestor| ancestor != outer)
        .any(|ancestor| {
            matches!(
                ancestor.kind(),
                SyntaxKind::SimpleLambdaExpression
                    | SyntaxKind::ParenthesizedLambdaExpression
                    | SyntaxKind::AnonymousMethodExpression
                    | SyntaxKind::LocalFunctionStatement
            )
        })
}

/// The type parameters a type mentions.
fn type_parameters_in(ty: &Type) -> Vec<SymbolId> {
    match ty {
        Type::TypeParameter(symbol) => vec![*symbol],
        Type::Named { type_arguments, .. } => {
            type_arguments.iter().flat_map(type_parameters_in).collect()
        }
        Type::Array { element, .. } | Type::Pointer(element) | Type::ByRef(element) => {
            type_parameters_in(element)
        }
        Type::Tuple(elements) => elements
            .iter()
            .flat_map(|element| type_parameters_in(&element.ty))
            .collect(),
        _ => Vec::new(),
    }
}

/// The edits for one target: the call where the selection was, and the new
/// method or local function.
fn write(
    context: &mut Context<'_, '_>,
    selection: &Selection,
    plan: &Plan,
    target: Target,
) -> Option<Vec<TextEdit>> {
    let newline = context.newline();
    let unit = context.indent_unit();
    let member = &plan.member;
    let member_indent = context.indentation_at(member.span().start());

    // Where it goes, and how far in its body is. A separate method cannot
    // call the member's local functions.
    let (insert_at, indent) = match target {
        Target::Method if plan.uses_local_function => return None,
        Target::Method => (member.span().end(), member_indent.clone()),
        Target::LocalFunction => {
            if plan
                .type_parameters
                .iter()
                .any(|(_, clause)| clause.is_some())
            {
                return None;
            }
            let body = member.child_of_kind(SyntaxKind::Block)?;
            let close = body.child_token_of_kind(SyntaxKind::CloseBraceToken)?;
            if close.is_missing() {
                return None;
            }
            let last = statements_of(&body).last()?.clone();
            (last.span().end(), format!("{member_indent}{unit}"))
        }
    };
    let body_indent = format!("{indent}{unit}");

    let taken = context.view.names_near(member);
    let name = fresh_name("NewMethod", &taken);

    // The new method's parameters and the call's arguments.
    let mut parameters = Vec::new();
    let mut arguments = Vec::new();
    let mut locals = Vec::new();
    let mut returned: Option<&Usage> = None;
    let mut declared_at_call = false;
    for (usage, flow) in &plan.flows {
        let ty = context.view.display_type(&usage.ty, member)?;
        match flow {
            Flow::In => {
                parameters.push(format!("{ty} {}", usage.name));
                arguments.push(usage.name.clone());
            }
            Flow::Ref => {
                parameters.push(format!("ref {ty} {}", usage.name));
                arguments.push(format!("ref {}", usage.name));
            }
            Flow::Out => {
                parameters.push(format!("out {ty} {}", usage.name));
                arguments.push(format!("out {}", usage.name));
            }
            Flow::Local => locals.push((usage, ty)),
            Flow::Returned => {
                returned = Some(usage);
                if usage.assigned_first.is_some() {
                    locals.push((usage, ty));
                } else {
                    parameters.push(format!("{ty} {}", usage.name));
                    arguments.push(usage.name.clone());
                }
            }
            Flow::ReturnedDeclaration => {
                returned = Some(usage);
                declared_at_call = true;
            }
        }
    }

    // The body: the selection, moved in.
    let mut body = String::new();
    let selection_span = selection.span();
    let original_indent = context.indentation_at(selection_span.start());
    match selection {
        Selection::Statements(_) => {
            // A variable assigned first at the top of the selection is
            // declared by that assignment; one assigned only deeper in is
            // declared ahead of it.
            let mut inner_edits = Vec::new();
            for (usage, ty) in &locals {
                match usage.assigned_first {
                    Some(at) => inner_edits.push(TextEdit::insert(
                        at.start() - selection_span.start(),
                        format!("{ty} "),
                    )),
                    None => {
                        body.push_str(&format!("{body_indent}{ty} {};{newline}", usage.name));
                    }
                }
            }
            let moved = crate::edit::apply(context.slice(selection_span), &inner_edits);
            body.push_str(&body_indent);
            body.push_str(&reindent(&moved, &original_indent, &body_indent));
            if let Some(usage) = returned {
                body.push_str(&format!("{newline}{body_indent}return {};", usage.name));
            }
        }
        Selection::Expression(node) => {
            let value = skip_parentheses(node).text();
            let moved = reindent(&value, &original_indent, &body_indent);
            body.push_str(&format!("{body_indent}return {moved};"));
        }
    }

    // The declaration.
    let mut modifiers = Vec::new();
    if target == Target::Method {
        modifiers.push("private");
    }
    let is_static = match target {
        Target::Method => plan.is_static,
        Target::LocalFunction => plan.is_static && !plan.uses_local_function,
    };
    if is_static {
        modifiers.push("static");
    }
    if plan.is_async {
        modifiers.push("async");
    }
    let generics = if target == Target::Method && !plan.type_parameters.is_empty() {
        let names: Vec<&str> = plan
            .type_parameters
            .iter()
            .map(|(name, _)| name.as_str())
            .collect();
        format!("<{}>", names.join(", "))
    } else {
        String::new()
    };
    let constraints: String = if target == Target::Method {
        plan.type_parameters
            .iter()
            .filter_map(|(_, clause)| clause.as_ref())
            .map(|clause| format!(" {clause}"))
            .collect()
    } else {
        String::new()
    };
    let declaration = format!(
        "{} {} {name}{generics}({}){constraints}{newline}{indent}{{{newline}{body}{newline}{indent}}}",
        modifiers.join(" "),
        plan.returns,
        parameters.join(", "),
    );
    let declaration = declaration.trim_start().to_string();
    let inserted = format!("{newline}{newline}{indent}{declaration}");

    // The call.
    let call = format!("{name}({})", arguments.join(", "));
    let call = if plan.is_async {
        format!("await {call}")
    } else {
        call
    };
    let replacement = match selection {
        Selection::Expression(node) => {
            let kind = if plan.is_async {
                SyntaxKind::AwaitExpression
            } else {
                SyntaxKind::InvocationExpression
            };
            parenthesized_for(&call, kind, node)
        }
        Selection::Statements(_) => {
            if plan.returns_through {
                format!("return {call};")
            } else if let Some(usage) = returned {
                if declared_at_call {
                    let ty = context.view.display_type(&usage.ty, member)?;
                    format!("{ty} {} = {call};", usage.name)
                } else {
                    format!("{} = {call};", usage.name)
                }
            } else {
                format!("{call};")
            }
        }
    };
    let mut edits = vec![TextEdit::new(selection_span, replacement)];
    if insert_at >= selection_span.end() || insert_at <= selection_span.start() {
        if target == Target::LocalFunction
            && selection_span.contains_span(TextSpan::new(insert_at, 0))
        {
            return None;
        }
        if target == Target::LocalFunction && insert_at == selection_span.end() {
            // The selection is the last statement: the local function goes
            // after the call that replaces it.
            edits[0].text.push_str(&inserted);
        } else {
            edits.push(TextEdit::insert(insert_at, inserted));
        }
    } else {
        return None;
    }
    if is_type_declaration(member.kind()) {
        return None;
    }
    Some(edits)
}

#[cfg(test)]
mod tests {
    use super::super::support::{apply, refuses};

    #[test]
    fn statements_become_a_static_method_taking_what_they_read() {
        let source = "class C\n{\n    void M(int a, int b)\n    {\n        [|int sum = a + b;\n        System.Console.WriteLine(sum);|]\n    }\n}\n";
        assert_eq!(
            apply(source, "Extract method"),
            "class C\n{\n    void M(int a, int b)\n    {\n        NewMethod(a, b);\n    }\n\n    private static void NewMethod(int a, int b)\n    {\n        int sum = a + b;\n        System.Console.WriteLine(sum);\n    }\n}\n"
        );
    }

    #[test]
    fn a_variable_declared_inside_and_used_after_is_returned() {
        let source = "class C\n{\n    int factor = 2;\n    int M(int a)\n    {\n        [|int doubled = a * factor;|]\n        return doubled + 1;\n    }\n}\n";
        assert_eq!(
            apply(source, "Extract method"),
            "class C\n{\n    int factor = 2;\n    int M(int a)\n    {\n        int doubled = NewMethod(a);\n        return doubled + 1;\n    }\n\n    private int NewMethod(int a)\n    {\n        int doubled = a * factor;\n        return doubled;\n    }\n}\n"
        );
    }

    #[test]
    fn a_variable_assigned_inside_and_read_after_comes_back() {
        let source = "class C\n{\n    int M(int a)\n    {\n        int total = 0;\n        [|total = a * 2;\n        total++;|]\n        return total;\n    }\n}\n";
        assert_eq!(
            apply(source, "Extract method"),
            "class C\n{\n    int M(int a)\n    {\n        int total = 0;\n        total = NewMethod(a);\n        return total;\n    }\n\n    private static int NewMethod(int a)\n    {\n        int total = a * 2;\n        total++;\n        return total;\n    }\n}\n"
        );
    }

    #[test]
    fn two_results_go_through_ref_and_out() {
        let source = "class C\n{\n    void M(int a)\n    {\n        int x = 0, y;\n        [|x += a;\n        y = a;|]\n        System.Console.WriteLine(x + y);\n    }\n}\n";
        assert_eq!(
            apply(source, "Extract method"),
            "class C\n{\n    void M(int a)\n    {\n        int x = 0, y;\n        NewMethod(a, ref x, out y);\n        System.Console.WriteLine(x + y);\n    }\n\n    private static void NewMethod(int a, ref int x, out int y)\n    {\n        x += a;\n        y = a;\n    }\n}\n"
        );
    }

    #[test]
    fn an_expression_becomes_a_method_returning_its_value() {
        let source = "class C\n{\n    bool M(string s)\n    {\n        return [|s.Length > 3|] && s != null;\n    }\n}\n";
        assert_eq!(
            apply(source, "Extract method"),
            "class C\n{\n    bool M(string s)\n    {\n        return NewMethod(s) && s != null;\n    }\n\n    private static bool NewMethod(string s)\n    {\n        return s.Length > 3;\n    }\n}\n"
        );
    }

    #[test]
    fn a_local_function_goes_at_the_end_of_the_body() {
        let source = "class C\n{\n    void M(int a)\n    {\n        [|System.Console.WriteLine(a);|]\n        System.Console.WriteLine(0);\n    }\n}\n";
        assert_eq!(
            apply(source, "Extract local function"),
            "class C\n{\n    void M(int a)\n    {\n        NewMethod(a);\n        System.Console.WriteLine(0);\n\n        static void NewMethod(int a)\n        {\n            System.Console.WriteLine(a);\n        }\n    }\n}\n"
        );
    }

    #[test]
    fn a_return_at_the_end_returns_through_the_call() {
        let source = "class C\n{\n    int M(int a)\n    {\n        System.Console.WriteLine(a);\n        [|if (a > 0)\n        {\n            return 1;\n        }\n        return 2;|]\n    }\n}\n";
        assert_eq!(
            apply(source, "Extract method"),
            "class C\n{\n    int M(int a)\n    {\n        System.Console.WriteLine(a);\n        return NewMethod(a);\n    }\n\n    private static int NewMethod(int a)\n    {\n        if (a > 0)\n        {\n            return 1;\n        }\n        return 2;\n    }\n}\n"
        );
    }

    #[test]
    fn a_generic_method_passes_its_type_parameter_on() {
        let source = "class C\n{\n    T M<T>(T value) where T : class\n    {\n        [|T copy = value;|]\n        return copy;\n    }\n}\n";
        assert_eq!(
            apply(source, "Extract method"),
            "class C\n{\n    T M<T>(T value) where T : class\n    {\n        T copy = NewMethod(value);\n        return copy;\n    }\n\n    private static T NewMethod<T>(T value) where T : class\n    {\n        T copy = value;\n        return copy;\n    }\n}\n"
        );
    }

    #[test]
    fn an_await_makes_it_async() {
        let source = "using System.Threading.Tasks;\nnamespace System.Threading.Tasks { public class Task { public static Task Delay(int ms) => null; } }\nclass C\n{\n    async Task M(int ms)\n    {\n        [|await Task.Delay(ms);|]\n    }\n}\n";
        assert_eq!(
            apply(source, "Extract method"),
            "using System.Threading.Tasks;\nnamespace System.Threading.Tasks { public class Task { public static Task Delay(int ms) => null; } }\nclass C\n{\n    async Task M(int ms)\n    {\n        await NewMethod(ms);\n    }\n\n    private static async Task NewMethod(int ms)\n    {\n        await Task.Delay(ms);\n    }\n}\n"
        );
    }

    #[test]
    fn a_file_with_crlf_gets_crlf() {
        let source = "class C\r\n{\r\n    void M(int a)\r\n    {\r\n        [|System.Console.WriteLine(a);|]\r\n    }\r\n}\r\n";
        assert_eq!(
            apply(source, "Extract method"),
            "class C\r\n{\r\n    void M(int a)\r\n    {\r\n        NewMethod(a);\r\n    }\r\n\r\n    private static void NewMethod(int a)\r\n    {\r\n        System.Console.WriteLine(a);\r\n    }\r\n}\r\n"
        );
    }

    #[test]
    fn leaving_the_selection_is_refused() {
        refuses(
            "class C\n{\n    void M(int[] items)\n    {\n        foreach (var item in items)\n        {\n            [|if (item > 0) break;|]\n        }\n    }\n}\n",
            "Extract method",
        );
        refuses(
            "class C\n{\n    int M(int a)\n    {\n        [|if (a > 0) return 1;|]\n        return 2;\n    }\n}\n",
            "Extract method",
        );
        refuses(
            "class C\n{\n    void M(int a)\n    {\n        [|int x = a;\n        System.Console|].WriteLine(x);\n    }\n}\n",
            "Extract method",
        );
    }

    #[test]
    fn a_local_nothing_has_assigned_yet_is_not_moved_or_passed() {
        // Returned from the new method, `result` would be read unassigned.
        refuses(
            "class C\n{\n    int M(bool b)\n    {\n        [|int result;|]\n        result = 1;\n        return result;\n    }\n}\n",
            "Extract method",
        );
        // Passed in to be written, it would be read unassigned at the call.
        refuses(
            "class C\n{\n    int M(bool b)\n    {\n        int result;\n        [|if (b) result = 1; else result = 2;|]\n        return result;\n    }\n}\n",
            "Extract method",
        );
    }

    #[test]
    fn an_assignment_that_reads_its_own_target_passes_it_in() {
        let source = "class C\n{\n    int M(int size)\n    {\n        [|size = size + 1;|]\n        return size;\n    }\n}\n";
        assert_eq!(
            apply(source, "Extract method"),
            "class C\n{\n    int M(int size)\n    {\n        size = NewMethod(size);\n        return size;\n    }\n\n    private static int NewMethod(int size)\n    {\n        size = size + 1;\n        return size;\n    }\n}\n"
        );
    }

    #[test]
    fn a_write_read_in_the_next_iteration_comes_back() {
        let source = "class C\n{\n    void M()\n    {\n        int last = 0;\n        for (int i = 0; i < 3; i++)\n        {\n            System.Console.WriteLine(last);\n            [|last = i;|]\n        }\n    }\n}\n";
        assert_eq!(
            apply(source, "Extract method"),
            "class C\n{\n    void M()\n    {\n        int last = 0;\n        for (int i = 0; i < 3; i++)\n        {\n            System.Console.WriteLine(last);\n            last = NewMethod(i);\n        }\n    }\n\n    private static int NewMethod(int i)\n    {\n        int last = i;\n        return last;\n    }\n}\n"
        );
    }
}
