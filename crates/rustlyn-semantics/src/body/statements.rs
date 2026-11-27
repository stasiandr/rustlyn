//! Binding statements: blocks, declarations, `return`, `switch`, `using`,
//! `try` and `throw`.

use rustlyn_diagnostics::ErrorCode;
use rustlyn_syntax::{LanguageVersion, SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

use super::{BodyBinder, identifier_text, node_key, typeless};
use crate::binder::Diagnostics;
use crate::bound::{
    BoundCaseLabel, BoundCatch, BoundExpression, BoundExpressionKind, BoundPattern,
    BoundPatternKind, BoundStatement, BoundStatementKind, BoundSwitchLabel, BoundSwitchSection,
    BoundUsingResource, ConstantValue, LockScope,
};
use crate::corlib::SpecialType;
use crate::symbol::{Accessibility, MethodKind, Modifiers, SymbolId, SymbolKind, TypeKind};
use crate::types::Type;

impl BodyBinder<'_> {
    pub(super) fn bind_block(&mut self, node: &SyntaxNode) -> BoundStatement {
        self.push_scope();
        let statements = self.bind_statement_list(&node.children().collect::<Vec<_>>());
        self.pop_scope();
        BoundStatement::new(BoundStatementKind::Block(statements), node.span())
    }

    /// Binds a run of statements, giving a `using` declaration the rest of the
    /// run as its body.
    ///
    /// `using var f = Open();` means the same as `using (var f = Open()) { ...
    /// }` around everything after it, and settling that here is what keeps
    /// both backends from having to work out where the scope ends.
    pub(super) fn bind_statement_list(&mut self, statements: &[SyntaxNode]) -> Vec<BoundStatement> {
        let mut bound = Vec::with_capacity(statements.len());
        for (index, labeled) in statements.iter().enumerate() {
            // `done: using var f = Open();` is labeled, and still holds `f`
            // to the end of the run: the labels go first, then the `using`.
            let mut statement = labeled.clone();
            let mut labels = Vec::new();
            while statement.kind() == SyntaxKind::LabeledStatement
                && let Some(inner) = statement
                    .children()
                    .find(|child| child.kind().is_statement_node())
            {
                labels.push(BoundStatement::new(
                    BoundStatementKind::Label(identifier_text(&statement).unwrap_or_default()),
                    statement.span(),
                ));
                statement = inner;
            }
            let statement = &statement;
            if statement.kind() == SyntaxKind::LocalDeclarationStatement
                && statement
                    .child_tokens()
                    .any(|token| token.kind() == SyntaxKind::UsingKeyword)
            {
                bound.extend(labels);
                let resources = statement
                    .child_of_kind(SyntaxKind::VariableDeclaration)
                    .map(|declaration| self.bind_using_resources(&declaration))
                    .unwrap_or_default();
                self.check_disposable(statement, &resources, statement.span());
                let resources = if awaits(statement) {
                    self.dispose_asynchronously(resources, statement.span())
                } else {
                    self.dispose_dynamic(resources)
                };
                let rest = self.bind_statement_list(&statements[index + 1..]);
                let span = statement.span();
                bound.push(BoundStatement::new(
                    BoundStatementKind::Using {
                        resources,
                        body: Box::new(BoundStatement::new(BoundStatementKind::Block(rest), span)),
                    },
                    span,
                ));
                return bound;
            }
            bound.push(self.bind_statement(labeled));
        }
        bound
    }

    pub(super) fn bind_statement(&mut self, node: &SyntaxNode) -> BoundStatement {
        self.synthetic_span = node.span();
        let kind = self.bind_statement_core(node);
        BoundStatement::new(kind, node.span())
    }

    /// A statement that is the body of another: the branch of an `if`, the
    /// body of a loop.
    ///
    /// Written without braces, it still gets a scope of its own (§7.7.1):
    /// `else if (Has(out bool when))` declares its `when` inside the `else`,
    /// and the next `if` in the block may declare one too. A block brings
    /// its own scope, so nothing is added around one.
    /// Whether the parser complained about anything in `node`: what it
    /// made of broken code is a guess, and judging the guess would only add
    /// to the complaint.
    fn has_syntax_error(&self, node: &SyntaxNode) -> bool {
        let span = node.span();
        self.binder
            .compilation()
            .trees()
            .get(self.tree)
            .is_some_and(|tree| {
                tree.diagnostics().iter().any(|diagnostic| {
                    let at = diagnostic.span();
                    at.start() >= span.start() && at.start() <= span.end()
                })
            })
    }

    fn bind_embedded_statement(&mut self, node: &SyntaxNode) -> BoundStatement {
        if node.kind() == SyntaxKind::Block {
            return self.bind_statement(node);
        }
        match node.kind() {
            // `if (b) int x = 1;` declares something nothing can see.
            SyntaxKind::LocalDeclarationStatement
            | SyntaxKind::LabeledStatement
            | SyntaxKind::LocalFunctionStatement => {
                self.report(ErrorCode::ErrBadEmbeddedStmt, node.span(), &[]);
            }
            // `if (b);` is almost always a stray semicolon. A loop's is
            // only suspicious where a block follows it: `while (b); { }`.
            SyntaxKind::EmptyStatement if !node.span().is_empty() => {
                let parent = node.parent();
                let is_loop = parent.is_some_and(|parent| {
                    matches!(
                        parent.kind(),
                        SyntaxKind::ForStatement
                            | SyntaxKind::ForEachStatement
                            | SyntaxKind::ForEachVariableStatement
                            | SyntaxKind::WhileStatement
                    )
                });
                let block_follows = parent
                    .and_then(|looping| {
                        let holder = looping.parent()?;
                        let mut siblings = holder.children().skip_while(|child| child != looping);
                        siblings.next();
                        siblings.next()
                    })
                    .is_some_and(|next| next.kind() == SyntaxKind::Block);
                if !is_loop || block_follows {
                    self.report(
                        ErrorCode::WrnPossibleMistakenNullStatement,
                        node.span(),
                        &[],
                    );
                }
            }
            _ => {}
        }
        self.push_scope();
        let bound = self.bind_statement(node);
        self.pop_scope();
        bound
    }

    fn bind_statement_core(&mut self, node: &SyntaxNode) -> BoundStatementKind {
        match node.kind() {
            SyntaxKind::Block => self.bind_block(node).kind,
            // `checked`, `unchecked` and `unsafe` each wrap a block and say
            // something about how what is in it runs. `unsafe` changes nothing
            // the runtime can see; the other two decide whether arithmetic
            // traps, which this backend does not model either way. The block
            // is all there is to bind.
            SyntaxKind::CheckedStatement
            | SyntaxKind::UncheckedStatement
            | SyntaxKind::UnsafeStatement => {
                if node.kind() != SyntaxKind::UnsafeStatement {
                    self.body
                        .checked_regions
                        .push((node.span(), node.kind() == SyntaxKind::CheckedStatement));
                }
                match node.child_of_kind(SyntaxKind::Block) {
                    Some(block) => self.bind_block(&block).kind,
                    None => BoundStatementKind::Empty,
                }
            }
            SyntaxKind::EmptyStatement => BoundStatementKind::Empty,
            SyntaxKind::LocalDeclarationStatement => {
                match node.child_of_kind(SyntaxKind::VariableDeclaration) {
                    Some(declaration) => {
                        let mut declared = self.bind_variable_declaration(&declaration);
                        if node
                            .child_tokens()
                            .any(|token| token.kind() == SyntaxKind::ConstKeyword)
                        {
                            self.note_constant_locals(&declared);
                        }
                        // `int a = 1, b = 2;` declares two; the block keeps
                        // them in the order they were written.
                        if declared.len() == 1 {
                            declared.pop().expect("just checked the length").kind
                        } else {
                            BoundStatementKind::Block(declared)
                        }
                    }
                    None => BoundStatementKind::Unsupported(node.kind()),
                }
            }
            SyntaxKind::ExpressionStatement => match node.children().next() {
                Some(expression) => {
                    let floor = self.body.diagnostics.len();
                    let value = self.bind_expression(&expression);
                    // `x + 1;` computes something and drops it. Said only
                    // of an expression that bound cleanly: a broken one has
                    // been complained about already.
                    if !is_statement_expression(&expression, &value)
                        && !self.body.diagnostics[floor..]
                            .iter()
                            .any(|(_, diagnostic)| diagnostic.is_error())
                        && !self.has_syntax_error(node)
                    {
                        self.report(ErrorCode::ErrIllegalStatement, expression.span(), &[]);
                    }
                    self.check_unawaited(&expression, &value);
                    let value = unused_deconstruction(&expression, value);
                    // `Debug.Assert(...)` is written out of the program where
                    // `DEBUG` is not defined: the call goes, and so does
                    // everything that would have been evaluated for it. A
                    // conditional method returns `void`, so a statement is the
                    // only place one can be called from.
                    if self.is_conditioned_out(&value) {
                        BoundStatementKind::Empty
                    } else {
                        BoundStatementKind::Expression(value)
                    }
                }
                None => BoundStatementKind::Empty,
            },
            SyntaxKind::IfStatement => {
                let mut children = node.children();
                let condition = self.bind_condition(children.next().as_ref());
                let consequence = children
                    .next()
                    .map(|branch| Box::new(self.bind_embedded_statement(&branch)));
                // The `else` is a clause of its own, holding one statement.
                let alternative = children.next().and_then(|clause| {
                    clause
                        .children()
                        .next()
                        .map(|branch| Box::new(self.bind_embedded_statement(&branch)))
                });
                match consequence {
                    Some(consequence) => BoundStatementKind::If {
                        condition,
                        consequence,
                        alternative,
                    },
                    None => BoundStatementKind::Unsupported(node.kind()),
                }
            }
            // What a loop's condition declares — `while (e is Access inner)`
            // — is the loop's own (§7.7.1): two loops in one block may both
            // write it, and neither can read the other's. An `if` is the odd
            // one out, and its condition's variables stay in scope after it.
            SyntaxKind::WhileStatement => {
                self.push_scope();
                let mut children = node.children();
                let condition = self.bind_condition(children.next().as_ref());
                let body = children
                    .next()
                    .map(|body| Box::new(self.bind_embedded_statement(&body)));
                self.pop_scope();
                match body {
                    Some(body) => BoundStatementKind::While { condition, body },
                    None => BoundStatementKind::Unsupported(node.kind()),
                }
            }
            SyntaxKind::DoStatement => {
                self.push_scope();
                let body = node
                    .children()
                    .find(|child| child.kind().is_statement_node());
                let condition = node
                    .children()
                    .find(|child| !child.kind().is_statement_node());
                let body = body.map(|body| Box::new(self.bind_embedded_statement(&body)));
                let condition = self.bind_condition(condition.as_ref());
                self.pop_scope();
                match body {
                    Some(body) => BoundStatementKind::DoWhile { body, condition },
                    None => BoundStatementKind::Unsupported(node.kind()),
                }
            }
            SyntaxKind::ForStatement => {
                self.push_scope();
                let mut initializers = Vec::new();
                let mut condition = None;
                let mut incrementors = Vec::new();
                let mut body = None;
                // A `for` is three comma-separated groups and a body, and the
                // parser leaves them as siblings; the two semicolons are what
                // separate the groups, and `for (Log(); Log(); )` has an
                // initializer and a condition of the same type.
                let semicolons: Vec<u32> = node
                    .child_tokens()
                    .filter(|token| token.kind() == SyntaxKind::SemicolonToken)
                    .map(|token| token.span().start())
                    .collect();
                let group = |start: u32| semicolons.iter().filter(|at| **at < start).count();
                for child in node.children() {
                    match child.kind() {
                        SyntaxKind::VariableDeclaration => {
                            initializers.extend(self.bind_variable_declaration(&child));
                        }
                        kind if kind.is_statement_node() => {
                            body = Some(Box::new(self.bind_embedded_statement(&child)));
                        }
                        _ => {
                            let expression = self.bind_expression(&child);
                            match group(child.span().start()) {
                                0 => initializers.push(BoundStatement::new(
                                    BoundStatementKind::Expression(unused_deconstruction(
                                        &child, expression,
                                    )),
                                    child.span(),
                                )),
                                1 if condition.is_none() => {
                                    condition = Some(self.as_condition(&child, expression));
                                }
                                _ => incrementors.push(unused_deconstruction(&child, expression)),
                            }
                        }
                    }
                }
                self.pop_scope();
                match body {
                    Some(body) => BoundStatementKind::For {
                        initializers,
                        condition,
                        incrementors,
                        body,
                    },
                    None => BoundStatementKind::Unsupported(node.kind()),
                }
            }
            SyntaxKind::ForEachStatement | SyntaxKind::ForEachVariableStatement => {
                self.bind_foreach(node)
            }
            SyntaxKind::ReturnStatement => {
                if self.in_finally(node) {
                    self.report_finally_leave(node);
                }
                match node.children().next() {
                    Some(expression) => {
                        let value = self.bind_expression(&expression);
                        let value = unused_deconstruction(&expression, value);
                        self.check_return(&expression, &value);
                        // `long M() { return 1; }` returns a `long`, and a backend
                        // handed an `int` there would write invalid IL. The
                        // conversion belongs here, where the expected type is.
                        let expected = self.expected_return();
                        let value = self.convert(value, &expected);
                        BoundStatementKind::Return(Some(value))
                    }
                    None => BoundStatementKind::Return(None),
                }
            }
            // `yield return e;` and `yield break;`. What `e` has to be comes
            // from what the method was declared to return: the `T` of its
            // `IEnumerable<T>`, or `object` where it named the untyped one.
            SyntaxKind::YieldReturnStatement => {
                let element = self.iterated_element();
                match node.children().find(|child| child.kind().is_expression()) {
                    Some(expression) => {
                        let value = self.bind_expression(&expression);
                        self.check_assignable(&expression, &value, &element);
                        let value = self.convert(value, &element);
                        BoundStatementKind::YieldReturn(value)
                    }
                    None => BoundStatementKind::Unsupported(node.kind()),
                }
            }
            SyntaxKind::YieldBreakStatement => {
                self.iterated_element();
                BoundStatementKind::YieldBreak
            }
            SyntaxKind::BreakStatement | SyntaxKind::ContinueStatement => self.bind_jump(node),
            // `Again:` names a place in this body, and `goto Again;` is a
            // jump to it. A label is a name of its own kind: it shares
            // nothing with a local, and lives for the whole body rather than
            // for the block it is written in.
            SyntaxKind::LabeledStatement => {
                let name = node
                    .child_tokens()
                    .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                    .map(|token| token.value_text().to_string())
                    .unwrap_or_default();
                let mut statements = vec![BoundStatement::new(
                    BoundStatementKind::Label(name),
                    node.span(),
                )];
                if let Some(inner) = node
                    .children()
                    .find(|child| child.kind().is_statement_node())
                {
                    statements.push(self.bind_statement(&inner));
                }
                BoundStatementKind::Block(statements)
            }
            SyntaxKind::GotoStatement => BoundStatementKind::Goto(
                node.child_tokens()
                    .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                    .map(|token| token.value_text().to_string())
                    .unwrap_or_default(),
            ),
            SyntaxKind::ThrowStatement => BoundStatementKind::Throw(
                node.children()
                    .next()
                    .map(|expression| self.bind_thrown(&expression)),
            ),
            // `goto case 3;` jumps to the section that handles 3, and carries
            // on from there. Only a constant can name one.
            SyntaxKind::GotoCaseStatement => {
                let value = node
                    .children()
                    .find(|child| child.kind().is_expression())
                    .map(|value| self.bind_expression(&value));
                // The value is one of the switch's type: `goto case new();`
                // on an `int` is `goto case 0;`.
                let governing = self.switch_types.last().cloned();
                let value = match (value, governing.clone()) {
                    (Some(value), Some(governing)) if typeless(&value) => {
                        Some(self.convert(value, &governing))
                    }
                    (value, _) => value,
                };
                // It names the label whose constant is tested the same way:
                // `goto case (uint)2` in a switch over an `object` is not the
                // `case (int)2` before it.
                let key = value.as_ref().and_then(|value| match &governing {
                    Some(governing) => self.binder.case_key(value, governing),
                    None => self
                        .binder
                        .folded(value)
                        .map(|constant| (value.ty.clone(), constant)),
                });
                match key {
                    Some(key) => BoundStatementKind::GotoCase(Some(key)),
                    None => BoundStatementKind::Unsupported(node.kind()),
                }
            }
            SyntaxKind::GotoDefaultStatement => BoundStatementKind::GotoCase(None),
            SyntaxKind::UsingStatement => self.bind_using_statement(node),
            SyntaxKind::LockStatement => {
                // What the locked expression declares (`lock (Get(out var
                // x))`) is in the enclosing scope, as an `if` condition's is.
                let value = node
                    .children()
                    .find(|child| child.kind().is_expression())
                    .map(|value| self.bind_expression(&value));
                self.push_scope();
                let object = self.special(SpecialType::Object);
                let boolean = self.special(SpecialType::Boolean);
                // A `Lock` is entered for a scope that is disposed, and the
                // local holds that scope instead of the object.
                let scope = value.as_ref().and_then(|value| self.lock_scope(&value.ty));
                let held_type = scope.as_ref().map_or(object, |scope| scope.ty.clone());
                let held = self.declare_synthetic_local("lock", held_type);
                let taken = self.declare_synthetic_local("taken", boolean);
                let body = node
                    .children()
                    .find(|child| child.kind().is_statement_node())
                    .map(|body| self.bind_statement(&body));
                self.pop_scope();
                match (value, body) {
                    (Some(value), Some(body)) => BoundStatementKind::Lock {
                        value,
                        held,
                        taken,
                        scope,
                        body: Box::new(body),
                    },
                    _ => BoundStatementKind::Unsupported(node.kind()),
                }
            }
            SyntaxKind::FixedStatement => {
                self.push_scope();
                let fixing = std::mem::replace(&mut self.fixing, true);
                let mut declarations = Vec::new();
                let mut body = None;
                for child in node.children() {
                    match child.kind() {
                        SyntaxKind::VariableDeclaration => {
                            declarations.extend(self.bind_variable_declaration(&child));
                        }
                        kind if kind.is_statement_node() => {
                            body = Some(self.bind_statement(&child));
                        }
                        _ => {
                            self.bind_expression(&child);
                        }
                    }
                }
                self.fixing = fixing;
                self.pop_scope();
                BoundStatementKind::Fixed {
                    declarations,
                    body: Box::new(body.unwrap_or_else(|| {
                        BoundStatement::new(BoundStatementKind::Empty, node.span())
                    })),
                }
            }
            SyntaxKind::LocalFunctionStatement => {
                // A local function has its own scope; its parameters are
                // declared symbols, like any other method's. Its body is
                // bound here, inside the method that holds it, so that the
                // locals of that method are in scope — a local function can
                // read them, which is the whole difference between one and a
                // private method. Running the statement does nothing: a
                // declaration is not an action.
                self.bind_local_function(node);
                BoundStatementKind::Empty
            }
            SyntaxKind::SwitchStatement => self.bind_switch_statement(node),
            SyntaxKind::TryStatement => self.bind_try_statement(node),
            _ => {
                // Everything else — try/catch, yield, checked blocks — is
                // bound by walking into it, so the names inside resolve even
                // though the control flow is not modelled.
                for child in node.children() {
                    if child.kind().is_statement_node() {
                        self.bind_statement(&child);
                    } else if child.kind().is_expression_node() {
                        self.bind_expression(&child);
                    } else {
                        self.bind_nested(&child);
                    }
                }
                BoundStatementKind::Unsupported(node.kind())
            }
        }
    }

    /// Walks a clause that is neither a statement nor an expression, such as a
    /// `catch` or an `else`.
    fn bind_nested(&mut self, node: &SyntaxNode) {
        self.push_scope();
        for child in node.children() {
            if child.kind().is_statement_node() {
                self.bind_statement(&child);
            } else if child.kind().is_expression() {
                self.bind_expression(&child);
            } else if child.kind() == SyntaxKind::CatchDeclaration {
                let ty = child
                    .children()
                    .find(|part| part.kind().is_type_node())
                    .map_or(Type::Error, |ty| self.resolve(&ty));
                if let Some(token) = child
                    .child_tokens()
                    .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                {
                    self.declare_local(token.value_text(), ty, token.span());
                }
            } else {
                self.bind_nested(&child);
            }
        }
        self.pop_scope();
    }

    fn bind_variable_declaration(&mut self, declaration: &SyntaxNode) -> Vec<BoundStatement> {
        let type_node = declaration
            .children()
            .find(|child| child.kind().is_type_node());
        // `scoped var s = ...` and `scoped ref int r = ...`: `scoped` says how
        // far the value may escape, and nothing about its type.
        let type_node = type_node.map(|node| match node.kind() {
            SyntaxKind::ScopedType => node
                .children()
                .find(|child| child.kind().is_type_node())
                .unwrap_or(node),
            _ => node,
        });
        // `ref int x = ref a[0];` names a place rather than a copy. The `ref`
        // is on the type here and on the value on the other side of the `=`.
        let by_ref = type_node
            .as_ref()
            .is_some_and(|node| node.kind() == SyntaxKind::RefType);
        let readonly_ref = type_node.as_ref().is_some_and(|node| {
            node.kind() == SyntaxKind::RefType
                && node
                    .child_tokens()
                    .any(|token| token.kind() == SyntaxKind::ReadOnlyKeyword)
        });
        let type_node = type_node.map(|node| match node.kind() {
            SyntaxKind::RefType => node
                .children()
                .find(|child| child.kind().is_type_node())
                .unwrap_or(node),
            _ => node,
        });
        let declared_var = type_node.as_ref().is_some_and(|node| node.text() == "var");
        let declared = match &type_node {
            Some(node) if !declared_var => self.resolve(node),
            _ => Type::Error,
        };

        let mut statements = Vec::new();
        for declarator in declaration.children() {
            if declarator.kind() != SyntaxKind::VariableDeclarator {
                continue;
            }
            let Some(token) = declarator
                .child_tokens()
                .find(|token| token.kind() == SyntaxKind::IdentifierToken)
            else {
                continue;
            };

            let initializer = declarator
                .child_of_kind(SyntaxKind::EqualsValueClause)
                .and_then(|clause| clause.children().next());
            // A local with a written type is in scope in its own
            // initializer: `TLocalState saved = saved = State.Clone();` is
            // how Roslyn writes one it means to read back. A `var` is not,
            // because until the initializer is bound it has no type.
            let early = (!declared_var && !self.fixing)
                .then(|| self.declare_local(token.value_text(), declared.clone(), token.span()));
            let initial = initializer.as_ref().map(|expression| {
                if expression.kind() == SyntaxKind::ArrayInitializerExpression
                    && matches!(declared, Type::Array { .. })
                {
                    self.bind_array_creation_as(expression, Some(&declared))
                } else {
                    self.bind_expression(expression)
                }
            });

            // `var f = static (Binder b, int n) => ...;` has a type of its own
            // (C# 10, §10.2.15): a `Func<Binder, int, R>` where every
            // parameter is written and `R` is what the body returns, or an
            // `Action<...>` where it returns nothing.
            let initial = match initial {
                Some(value)
                    if declared_var
                        && matches!(
                            value.kind,
                            BoundExpressionKind::UnboundLambda(_)
                                | BoundExpressionKind::MethodGroup { .. }
                        ) =>
                {
                    match self.natural_function_type(&value) {
                        Some(natural) => Some(self.convert(value, &natural)),
                        None => {
                            // A group of overloads, or a lambda whose
                            // parameters say no types, has none to give
                            // (CS8917); before C# 10 nothing of the kind
                            // did (CS0815).
                            let expression =
                                initializer.as_ref().map_or(value.span, |node| node.span());
                            if self.language_version().at_least(LanguageVersion::CSharp10) {
                                self.report(ErrorCode::ErrCannotInferDelegateType, expression, &[]);
                            } else {
                                let what = if matches!(
                                    value.kind,
                                    BoundExpressionKind::MethodGroup { .. }
                                ) {
                                    "method group"
                                } else {
                                    "lambda expression"
                                };
                                self.report(
                                    ErrorCode::ErrImplicitlyTypedVariableAssignedBadValue,
                                    declarator.span(),
                                    &[what],
                                );
                            }
                            Some(BoundExpression::error(value.span))
                        }
                    }
                }
                other => other,
            };

            // `var x;` and `var x = null;` give it nothing to take a type
            // from. A type of the user's called `var` would, and then this
            // is not a `var` at all.
            if declared_var && !self.fixing && self.binder.lookup("var", 0, &self.context).is_none()
            {
                match &initializer {
                    None => self.report(
                        ErrorCode::ErrImplicitlyTypedVariableWithNoInitializer,
                        token.span(),
                        &[],
                    ),
                    Some(value) if value.kind() == SyntaxKind::NullLiteralExpression => {
                        self.report(
                            ErrorCode::ErrImplicitlyTypedVariableAssignedBadValue,
                            declarator.span(),
                            &["<null>"],
                        );
                    }
                    Some(_) => {}
                }
            }

            // `var` takes the type of whatever it is given.
            let ty = if declared_var {
                initial
                    .as_ref()
                    .map_or(Type::Error, |value| value.ty.clone())
            } else {
                declared.clone()
            };

            let initial = match (&initializer, initial) {
                // What is neither a string, an array nor a pointer is pinned
                // through the reference its `GetPinnableReference` hands back
                // (C# 7.3), an extension one included.
                (Some(_), Some(value))
                    if self.fixing
                        && matches!(declared, Type::Pointer(_))
                        && !matches!(
                            value.ty,
                            Type::Pointer(_) | Type::Array { .. } | Type::Error
                        )
                        && self.binder.special_of(&value.ty) != Some(SpecialType::String) =>
                {
                    match self.pinnable_reference(value.clone(), &mut statements) {
                        Some(call) => Some(call),
                        None => {
                            self.check_assignable(
                                initializer.as_ref().expect("matched a value"),
                                &value,
                                &ty,
                            );
                            Some(self.convert(value, &ty))
                        }
                    }
                }
                // `fixed (char* p = text)` and `fixed (byte* p = bytes)` are
                // the one place a string or an array is a pointer, and what
                // makes them one is the `fixed` rather than the types.
                (Some(_), Some(value)) if self.fixing && pins_to(&declared, &value.ty) => {
                    Some(self.pinnable_through_extension(value, &declared))
                }
                (Some(expression), Some(value)) if !declared_var => {
                    self.check_assignable(expression, &value, &ty);
                    Some(self.convert(value, &ty))
                }
                (_, value) => value,
            };

            let local =
                early.unwrap_or_else(|| self.declare_local(token.value_text(), ty, token.span()));
            if by_ref && let Some(slot) = self.body.locals.get_mut(local.0 as usize) {
                slot.by_ref = true;
                slot.readonly_ref = readonly_ref;
            }
            statements.push(BoundStatement::new(
                BoundStatementKind::LocalDeclaration {
                    local,
                    initializer: initial,
                },
                declarator.span(),
            ));
        }
        statements
    }

    pub(super) fn check_assignable(
        &mut self,
        node: &SyntaxNode,
        value: &BoundExpression,
        to: &Type,
    ) {
        let from = &value.ty;
        if to.is_error() || from.is_error() {
            return;
        }
        // An operand that divided by zero or overflowed has no value, and
        // the error about it is the only one: what it would have been
        // converted to is nobody's business.
        if self.reported_within(value.span) {
            return;
        }
        // Parentheses, `checked` and `unchecked` bind to what they hold, and
        // the error is about that: `byte b = unchecked(256);` is at the 256.
        let original = node;
        let node = &inside_wrappers(node);
        // `stackalloc T[n]` reaches a `Span<T>` (§12.8.22).
        if let BoundExpressionKind::StackAlloc { element, .. } = &value.kind
            && self.is_span_of(to, element)
        {
            return;
        }
        if (matches!(value.kind, BoundExpressionKind::InterpolatedString(_))
            && self.is_formattable(to))
            || (value.is_interpolated_string() && self.is_handler_type(to))
        {
            return;
        }
        // `ulong f = n switch { 0 => 1, _ => 2 }` reaches the `ulong` arm by
        // arm, whatever type the arms settled on between themselves; the
        // conversion binds the switch again with the target.
        if let BoundExpressionKind::Switch { arms, .. } = &value.kind
            && arms.iter().all(|arm| {
                arm.value.ty.is_error()
                    || matches!(arm.value.ty, Type::Null)
                    || self.binder.converts_implicitly(&arm.value.ty, to)
                    || self.constant_fits(&arm.value, to)
                    || (arm.value.is_interpolated_string() && self.is_handler_type(to))
            })
        {
            return;
        }
        if !self.binder.converts_implicitly(from, to)
            && !self.constant_fits(value, to)
            && self.constant_operator(value, to).is_none()
            && self.tuple_literal_operator(value, to).is_none()
        {
            // An `int` constant that does not fit a smaller integral type is
            // CS0031, not CS0266: Roslyn reports the value itself. The `int`
            // source is the only one that does (a `uint`, `long` or `char`
            // constant is CS0266), and so are the targets below (an enum or
            // `char` target is CS0266 too).
            if self.binder.special_of(from) == Some(SpecialType::Int32)
                && let Some(ConstantValue::Int32(number)) = self.binder.folded(value)
                && matches!(
                    self.binder.special_of(to),
                    Some(
                        SpecialType::SByte
                            | SpecialType::Byte
                            | SpecialType::Int16
                            | SpecialType::UInt16
                            | SpecialType::UInt32
                            | SpecialType::UInt64
                    )
                )
            {
                let to = self.display(to);
                self.report(
                    ErrorCode::ErrConstOutOfRange,
                    node.span(),
                    &[&number.to_string(), &to],
                );
                return;
            }
            // A negative `long` constant is no `ulong` either, and is the
            // value's error as well: only that pair of types converts a
            // constant of a `long` (a `uint` target is CS0266).
            if self.binder.special_of(from) == Some(SpecialType::Int64)
                && self.binder.special_of(to) == Some(SpecialType::UInt64)
                && let Some(number) = self
                    .binder
                    .folded(value)
                    .as_ref()
                    .and_then(crate::constant::as_exact)
                && number < 0
            {
                let to = self.display(to);
                self.report(
                    ErrorCode::ErrConstOutOfRange,
                    node.span(),
                    &[&number.to_string(), &to],
                );
                return;
            }
            // A `double` literal, as written, where a `float` or a `decimal`
            // is wanted: it wants its suffix.
            let suffix = match self.binder.special_of(to) {
                Some(SpecialType::Single) => Some("F"),
                Some(SpecialType::Decimal) => Some("M"),
                _ => None,
            };
            let literal = inside_wrappers(original);
            if self.binder.special_of(from) == Some(SpecialType::Double)
                && literal.kind() == SyntaxKind::NumericLiteralExpression
                && let Some(suffix) = suffix
            {
                let to = self.display(to);
                self.report(ErrorCode::ErrLiteralDoubleCast, node.span(), &[suffix, &to]);
                return;
            }
            let code = if self.converts_explicitly(from, to) {
                ErrorCode::ErrNoImplicitConvCast
            } else {
                ErrorCode::ErrNoImplicitConv
            };
            let (from, to) = (self.display(from), self.display(to));
            self.report(code, node.span(), &[&from, &to]);
        }
    }

    /// What a `return` here has to produce.
    ///
    /// Inside a lambda that is the delegate's return type, not the enclosing
    /// method's — the lambda is a method of its own, however it is written.
    pub(super) fn expected_return(&self) -> Type {
        if let Some(frame) = self.lambdas.last() {
            return frame.return_type.clone();
        }
        let Some(member) = self.member else {
            return Type::Error;
        };
        // A constructor returns nothing, whatever its symbol's type says the
        // thing it makes is: `C(int x) => _x = x;` runs an expression, and a
        // `return` in one may carry no value.
        if matches!(
            self.binder.compilation().symbols().get(member).as_method(),
            Some(detail)
                if matches!(
                    detail.method_kind,
                    crate::symbol::MethodKind::Constructor
                        | crate::symbol::MethodKind::StaticConstructor
                        | crate::symbol::MethodKind::Destructor
                )
        ) {
            return Type::Void;
        }
        let mut sink = Diagnostics::new();
        // `ref T M() => ref x;` returns a variable of type `T`; the `ref` is
        // in the syntax on both sides and not in what is being converted.
        let declared = self.binder.type_of(member, &mut sink).value().clone();
        // An `async` method is written as returning a `Task<T>` and its
        // `return` statements give a `T`: the task is the compiler's, not the
        // source's.
        if self.is_async(member) {
            return self.task_result(&declared);
        }
        declared
    }

    pub(super) fn is_async(&self, member: SymbolId) -> bool {
        self.binder
            .compilation()
            .symbols()
            .get(member)
            .modifiers
            .contains(Modifiers::ASYNC)
    }

    /// The element type of the body being bound, recording that it is an
    /// iterator on the way.
    ///
    /// A `yield` anywhere makes the whole body one, and what it gives out is
    /// read off what the method says it returns: `IEnumerable<T>`,
    /// `IEnumerator<T>` and their untyped forms are the four the language
    /// allows (§15.15). The untyped ones give `object`. An `async` one
    /// returns `IAsyncEnumerable<T>` or `IAsyncEnumerator<T>` instead (C# 8),
    /// which have no untyped forms.
    fn iterated_element(&mut self) -> Type {
        let declared = match self.lambdas.last() {
            Some(frame) => frame.return_type.clone(),
            None => match self.member {
                Some(member) => {
                    let mut sink = Diagnostics::new();
                    self.binder.type_of(member, &mut sink).value().clone()
                }
                None => Type::Error,
            },
        };
        // A local function is a frame that declares itself; a lambda may
        // not `yield` at all.
        let asynchronous = match self.lambdas.last() {
            Some(frame) => frame
                .declares
                .is_some_and(|function| self.is_async(function)),
            None => self.member.is_some_and(|member| self.is_async(member)),
        };
        let element = match &declared {
            Type::Named {
                symbol,
                type_arguments,
            } => {
                let name = self
                    .binder
                    .compilation()
                    .symbols()
                    .get(*symbol)
                    .name
                    .clone();
                match (asynchronous, name.as_str()) {
                    (false, "IEnumerable" | "IEnumerator") => type_arguments
                        .first()
                        .cloned()
                        .unwrap_or_else(|| self.special(SpecialType::Object)),
                    (true, "IAsyncEnumerable" | "IAsyncEnumerator") => {
                        type_arguments.first().cloned().unwrap_or(Type::Error)
                    }
                    _ => Type::Error,
                }
            }
            _ => Type::Error,
        };
        // A `yield` inside a local function makes the function the
        // iterator, and says nothing about the method around it.
        match self.lambdas.last_mut() {
            Some(frame) => frame.iterator = Some(element.clone()),
            None => self.body.iterator = Some(element.clone()),
        }
        element
    }

    /// What an `async` method's `return` has to produce, given what it
    /// declares.    /// What an `async` method's `return` has to produce, given what it
    /// declares.
    pub(super) fn task_result(&self, declared: &Type) -> Type {
        let Type::Named {
            symbol,
            type_arguments,
        } = declared
        else {
            return declared.clone();
        };
        let name = self
            .binder
            .compilation()
            .symbols()
            .get(*symbol)
            .name
            .clone();
        // A task-like type, whose `[AsyncMethodBuilder]` names how it is
        // built, gives the same way (§15.15.1).
        if name != "Task"
            && name != "ValueTask"
            && self.binder.async_method_builder(*symbol).is_none()
        {
            return declared.clone();
        }
        // `async Task` returns nothing; `async Task<T>` returns a `T`.
        type_arguments.first().cloned().unwrap_or(Type::Void)
    }

    pub(super) fn check_return(&mut self, node: &SyntaxNode, value: &BoundExpression) {
        let expected = self.expected_return();
        if matches!(expected, Type::Void | Type::Error) {
            return;
        }
        self.check_assignable(node, value, &expected);
    }

    /// What a `throw` throws: an exception, which a `dynamic` value is
    /// converted to when it runs (§13.10.6).
    pub(super) fn bind_thrown(&mut self, node: &SyntaxNode) -> BoundExpression {
        let thrown = self.bind_expression(node);
        if matches!(thrown.ty, Type::Dynamic)
            && let Some(exception) = self.framework_type("System.Exception")
        {
            return self.convert(thrown, &exception);
        }
        thrown
    }

    /// `break;`, `continue;`, and the labeled `break outer;` and `continue
    /// outer;` of C# 15, which leave the loop (or, for `break`, the
    /// `switch`) the label is written on rather than the innermost one.
    ///
    /// The target is found the way it is written: the loops and switches
    /// around the statement, out to the function it is in — a lambda or a
    /// local function is a body of its own, and nothing is left through it.
    fn bind_jump(&mut self, node: &SyntaxNode) -> BoundStatementKind {
        let is_break = node.kind() == SyntaxKind::BreakStatement;
        let label = node
            .child_tokens()
            .find(|token| token.kind() == SyntaxKind::IdentifierToken && !token.span().is_empty());
        let name = label.as_ref().map(|token| token.value_text().to_string());
        let mut outward = 0;
        let mut in_finally = false;
        for ancestor in node.ancestors() {
            let counts = match ancestor.kind() {
                SyntaxKind::FinallyClause => {
                    in_finally = true;
                    false
                }
                SyntaxKind::WhileStatement
                | SyntaxKind::DoStatement
                | SyntaxKind::ForStatement
                | SyntaxKind::ForEachStatement
                | SyntaxKind::ForEachVariableStatement => true,
                SyntaxKind::SwitchStatement => is_break,
                kind if crate::flow::is_function_boundary(kind) => break,
                _ => false,
            };
            if !counts {
                continue;
            }
            let found = match &name {
                None => true,
                Some(name) => ancestor.parent().is_some_and(|parent| {
                    parent.kind() == SyntaxKind::LabeledStatement
                        && parent
                            .child_tokens()
                            .find(|token| token.kind() == SyntaxKind::IdentifierToken)
                            .is_some_and(|token| token.value_text() == name.as_str())
                }),
            };
            if found {
                if in_finally {
                    self.report_finally_leave(node);
                }
                return if is_break {
                    BoundStatementKind::Break(outward)
                } else {
                    BoundStatementKind::Continue(outward)
                };
            }
            outward += 1;
        }
        match (&label, &name) {
            (Some(label), Some(name)) => {
                let code = if is_break {
                    ErrorCode::ErrNoBreakId
                } else {
                    ErrorCode::ErrNoContinueId
                };
                self.report(code, label.span(), &[name]);
                // A label of that name elsewhere is still where the jump
                // was aimed, as far as what is reachable goes.
                if crate::flow::labels_in_function(node).contains(name) {
                    BoundStatementKind::Goto(name.clone())
                } else {
                    BoundStatementKind::Empty
                }
            }
            _ => {
                self.report(ErrorCode::ErrNoBreakOrCont, node.span(), &[]);
                BoundStatementKind::Empty
            }
        }
    }

    /// CS0157: a jump out of a `finally` would abandon whatever was leaving
    /// the `try` when the `finally` started, so none may leave it.
    fn report_finally_leave(&mut self, node: &SyntaxNode) {
        if let Some(first) = node.first_token() {
            self.report(ErrorCode::ErrBadFinallyLeave, first.span(), &[]);
        }
    }

    /// Whether a statement sits in a `finally` of the function it is in.
    fn in_finally(&mut self, node: &SyntaxNode) -> bool {
        // Up to the first `finally`, function boundary or node already
        // answered for; then every node passed has that answer too.
        let mut passed = vec![node_key(node)];
        let mut answer = false;
        let mut current = node.parent();
        while let Some(ancestor) = current {
            let at = node_key(ancestor);
            if let Some(&known) = self.in_finally_memo.get(&at) {
                answer = known;
                break;
            }
            if ancestor.kind() == SyntaxKind::FinallyClause {
                answer = true;
                break;
            }
            if crate::flow::is_function_boundary(ancestor.kind()) {
                break;
            }
            passed.push(at);
            current = ancestor.parent();
        }
        for at in passed {
            self.in_finally_memo.insert(at, answer);
        }
        answer
    }

    fn bind_switch_statement(&mut self, node: &SyntaxNode) -> BoundStatementKind {
        let governing = node
            .children()
            .find(|child| child.kind().is_expression())
            .map(|child| self.bind_expression(&child));
        let Some(governing) = governing else {
            return BoundStatementKind::Unsupported(node.kind());
        };
        let governing = self.switch_governing(governing);
        let input = governing.ty.clone();
        self.switch_types.push(input.clone());

        let mut opened = 0;
        let mut sections = Vec::new();
        for child in node.children() {
            if child.kind() != SyntaxKind::SwitchSection {
                continue;
            }
            // Beside the sections before it, not inside them: what they
            // declared stays in scope, and what this one declares is its own.
            self.push_sibling_scope();
            opened += 1;
            let mut labels = Vec::new();
            let mut statements = Vec::new();
            for part in child.children() {
                match part.kind() {
                    SyntaxKind::CaseSwitchLabel => {
                        let written = part.children().find(|child| child.kind().is_expression());
                        labels.push(match written {
                            // `case BoundArrayAccess:` and `case Kind.Red:`
                            // are the same syntax; only what the name means
                            // tells them apart, and a type is a test rather
                            // than a comparison (§13.8.3).
                            Some(written) if self.names_a_type(&written) => {
                                let ty = self.resolve(&written);
                                let pattern = self
                                    .union_type_test(&input, &ty, part.span())
                                    .unwrap_or_else(|| {
                                        BoundPattern::new(BoundPatternKind::Type(ty), part.span())
                                    });
                                BoundSwitchLabel::Case(Box::new(BoundCaseLabel {
                                    pattern,
                                    when: None,
                                }))
                            }
                            Some(written) => {
                                let value = self.bind_expression(&written);
                                // `case new():` is a value of the type
                                // switched on.
                                let value = if typeless(&value) {
                                    self.convert(value, &input)
                                } else {
                                    value
                                };
                                // `case Tests.Not:` is dotted, which reads
                                // as a member access, and the member it
                                // reaches is a nested type: a test too. The
                                // access knows the construction: `case
                                // G<B>.D:` tests for `G<B>.D`.
                                let pattern = match value.kind {
                                    BoundExpressionKind::TypeExpression(symbol) => {
                                        let ty = if value.ty.symbol() == Some(symbol) {
                                            value.ty
                                        } else {
                                            Type::named(symbol)
                                        };
                                        BoundPattern::new(BoundPatternKind::Type(ty), part.span())
                                    }
                                    // On a union, the constant is compared
                                    // with what it holds (C# 15).
                                    _ => match self.union_constant_test(&input, value, part.span())
                                    {
                                        Ok(pattern) => pattern,
                                        // `case "two":` on a span compares
                                        // what the characters are, as `span is
                                        // "two"` does.
                                        Err(value) => {
                                            let value =
                                                Box::new(self.constant_as_decimal(*value, &input));
                                            let kind = self
                                                .span_string_test(&value, &input, part.span())
                                                .unwrap_or(BoundPatternKind::Constant(*value));
                                            BoundPattern::new(kind, part.span())
                                        }
                                    },
                                };
                                BoundSwitchLabel::Case(Box::new(BoundCaseLabel {
                                    pattern,
                                    when: None,
                                }))
                            }
                            None => BoundSwitchLabel::Default,
                        });
                    }
                    SyntaxKind::CasePatternSwitchLabel => {
                        labels.push(self.bind_case_label(&part, &input));
                    }
                    SyntaxKind::DefaultSwitchLabel => labels.push(BoundSwitchLabel::Default),
                    kind if kind.is_statement_node() => {
                        statements.push(self.bind_statement(&part));
                    }
                    _ => {}
                }
            }
            sections.push(BoundSwitchSection { labels, statements });
        }
        for _ in 0..opened {
            self.pop_scope();
        }
        self.switch_types.pop();

        BoundStatementKind::Switch {
            governing,
            sections,
        }
    }

    /// Whether a switch on this type needs no conversion to be one on
    /// constants (§13.8.3): an integer, a `char`, a `string`, a `bool`, an
    /// enum, or a `T?` of one of them. As the target of a user-defined
    /// conversion, `bool` and an enum do not count.
    fn is_v6_governing_type(&self, ty: &Type, as_operator_target: bool) -> bool {
        let inner = self
            .binder
            .nullable_underlying(ty)
            .unwrap_or_else(|| ty.clone());
        if !as_operator_target && self.binder.enum_underlying(&inner).is_some() {
            return true;
        }
        match self.binder.special_of(&inner) {
            Some(
                SpecialType::SByte
                | SpecialType::Byte
                | SpecialType::Int16
                | SpecialType::UInt16
                | SpecialType::Int32
                | SpecialType::UInt32
                | SpecialType::Int64
                | SpecialType::UInt64
                | SpecialType::Char
                | SpecialType::String,
            ) => true,
            Some(SpecialType::Boolean) => !as_operator_target,
            _ => false,
        }
    }

    /// The value a `switch` statement switches on (§13.8.3): the expression
    /// itself where its type is one a switch on constants takes, and
    /// otherwise the result of the one implicit conversion its type
    /// declares to such a type — `switch (conv)` on a class with an
    /// `implicit operator int` switches on that `int`. With no such
    /// conversion it stays what it is and the labels are patterns.
    ///
    /// Like Roslyn (and the native compiler before it), the conversion with
    /// the least lifting wins: on an `A?`, `int(A?)` is preferred over
    /// `int?(A)` lifted to take the `A?`.
    fn switch_governing(&mut self, governing: BoundExpression) -> BoundExpression {
        if governing.ty.is_error() || self.is_v6_governing_type(&governing.ty, false) {
            return governing;
        }
        let source = governing.ty.clone();
        let underlying = self.binder.nullable_underlying(&source);
        let declaring = underlying.clone().unwrap_or_else(|| source.clone());
        let Some(symbol) = declaring.symbol() else {
            return governing;
        };
        if self.binder.special_of(&declaring).is_some() {
            return governing;
        }
        let symbols = self.binder.compilation().symbols();
        // Each candidate with whether it has to be lifted to take the source.
        let mut normal = Vec::new();
        let mut lifted = Vec::new();
        for operator in self.binder.lookup_member(symbol, "op_Implicit") {
            let Some(detail) = symbols.get(operator).as_method() else {
                continue;
            };
            let [parameter] = detail.parameters[..] else {
                continue;
            };
            let takes = self.member_type(parameter, &declaring);
            let gives = self.member_type(operator, &declaring);
            if takes == source
                || self.binder.converts_implicitly(&source, &takes)
                    && self.user_defined_conversion(&source, &takes).is_none()
            {
                if self.is_v6_governing_type(&gives, true) {
                    normal.push((operator, gives));
                }
            } else if underlying.as_ref() == Some(&takes) {
                let gives = if self.wraps_in_nullable(&gives) {
                    self.nullable_of(gives)
                } else {
                    gives
                };
                if self.is_v6_governing_type(&gives, true) {
                    lifted.push((operator, gives));
                }
            }
        }
        match (normal.as_slice(), lifted.as_slice()) {
            ([(operator, gives)], _) => self.operator_call(*operator, governing, gives.clone()),
            ([], [(operator, gives)]) => {
                let (operator, gives) = (*operator, gives.clone());
                let span = governing.span;
                self.lift_conversion(governing, &gives, |this, value| {
                    let result = this.member_type(operator, &value.ty.clone());
                    this.operator_call(operator, value, result)
                })
                .unwrap_or_else(|| BoundExpression::error(span))
            }
            _ => governing,
        }
    }

    fn bind_using_statement(&mut self, node: &SyntaxNode) -> BoundStatementKind {
        // The resource's name is in scope for the body and nowhere else.
        self.push_scope();
        let resources = match node.child_of_kind(SyntaxKind::VariableDeclaration) {
            Some(declaration) => {
                let resources = self.bind_using_resources(&declaration);
                self.check_disposable(node, &resources, declaration.span());
                resources
            }
            None => node
                .children()
                .find(|child| child.kind().is_expression())
                .map(|expression| {
                    // `using (Open())` names nothing, but the value still has
                    // to be kept until the end, so it gets a local anyway.
                    let value = self.bind_expression(&expression);
                    // `using (Open(1)) using (Open(2))` holds two such
                    // values in one scope, so the local cannot be one name
                    // that a second declaration would collide with.
                    let local = self.declare_synthetic_local("using", value.ty.clone());
                    let dispose = self.dispose_of(&value.ty);
                    let resources = vec![BoundUsingResource {
                        local,
                        value,
                        dispose,
                        awaited: None,
                    }];
                    self.check_disposable(node, &resources, expression.span());
                    resources
                })
                .unwrap_or_default(),
        };
        // `await using` disposes each resource with an awaited
        // `DisposeAsync`, found now, while the names are in scope.
        let resources = if awaits(node) {
            self.dispose_asynchronously(resources, node.span())
        } else {
            self.dispose_dynamic(resources)
        };
        let body = node
            .children()
            .find(|child| child.kind().is_statement_node())
            .map(|child| Box::new(self.bind_statement(&child)));
        self.pop_scope();

        match body {
            Some(body) => BoundStatementKind::Using { resources, body },
            None => BoundStatementKind::Unsupported(node.kind()),
        }
    }

    /// What `lock` calls on a value of this type where it is the framework's
    /// `System.Threading.Lock` (C# 13): `lock (l) { ... }` is `using
    /// (l.EnterScope()) { ... }` then, and everything else is `Monitor`.
    ///
    /// Roslyn goes by the name alone: a `System.Threading.Lock` is the one of
    /// any assembly, and its own members
    /// are looked at, not inherited ones: a public, non-static `EnterScope()`
    /// without type parameters that is the only such member and gives a value
    /// (not a `ref`), of a public `ref struct Scope` it declares, whose own
    /// public `Dispose()` that gives nothing is the only such member too. A
    /// type that has not got them is an error there (CS0656) and is locked
    /// as an object here.
    fn lock_scope(&self, ty: &Type) -> Option<LockScope> {
        let Type::Named {
            symbol,
            type_arguments,
            ..
        } = ty
        else {
            return None;
        };
        let symbols = self.binder.compilation().symbols();
        if !type_arguments.is_empty() || symbols.qualified_name(*symbol) != "System.Threading.Lock"
        {
            return None;
        }
        // What is locked is an object: a struct of that name is not entered
        // (and `callvirt` on it would be invalid).
        if !matches!(
            symbols.get(*symbol).type_kind(),
            Some(TypeKind::Class | TypeKind::Interface)
        ) {
            return None;
        }
        let only_member = |owner: SymbolId, name: &str| {
            let mut found = symbols
                .lookup(owner, name)
                .iter()
                .copied()
                .filter(|member| {
                    let member = symbols.get(*member);
                    member.kind == SymbolKind::Method
                        && member.accessibility == Accessibility::Public
                        && !member.modifiers.contains(Modifiers::STATIC)
                        && member.as_method().is_some_and(|method| {
                            method.parameters.is_empty()
                                && method.arity == 0
                                && method.method_kind == MethodKind::Ordinary
                        })
                });
            let first = found.next()?;
            found.next().is_none().then_some(first)
        };
        let enter = only_member(*symbol, "EnterScope")?;
        let returned = self.binder.type_of(enter, &mut Diagnostics::new());
        let Type::Named {
            symbol: scope,
            type_arguments,
            ..
        } = &returned
        else {
            return None;
        };
        let declared = symbols.get(*scope);
        if !type_arguments.is_empty()
            || declared.name != "Scope"
            || declared.container != Some(*symbol)
            || declared.accessibility != Accessibility::Public
            || declared.type_kind() != Some(TypeKind::Struct)
            || !declared
                .as_named_type()
                .is_some_and(|detail| detail.ref_like)
        {
            return None;
        }
        let dispose = only_member(*scope, "Dispose")?;
        if !matches!(
            self.binder.type_of(dispose, &mut Diagnostics::new()),
            Type::Void
        ) {
            return None;
        }
        Some(LockScope {
            enter,
            ty: returned,
            dispose,
        })
    }

    fn bind_using_resources(&mut self, declaration: &SyntaxNode) -> Vec<BoundUsingResource> {
        self.bind_variable_declaration(declaration)
            .into_iter()
            .filter_map(|statement| match statement.kind {
                BoundStatementKind::LocalDeclaration {
                    local,
                    initializer: Some(value),
                } => {
                    // What is disposed is the variable, as declared: `using
                    // (IDisposable i = null)` has a `null` for a value. It
                    // is read-only: a struct in a field of it is only ever
                    // copied from.
                    self.body.locals[local.0 as usize].readonly = true;
                    let declared = self.body.locals[local.0 as usize].ty.clone();
                    let dispose = self
                        .dispose_of(&declared)
                        .or_else(|| self.dispose_of(&value.ty));
                    Some(BoundUsingResource {
                        local,
                        value,
                        dispose,
                        awaited: None,
                    })
                }
                _ => None,
            })
            .collect()
    }

    /// The resources of a plain `using`, with a `dynamic` one followed by
    /// the `IDisposable` the runtime binder converts it to, which is what
    /// is disposed. The conversion happens as the resource is taken (Roslyn
    /// converts it into a temporary right after the declaration), so that
    /// one that fails does so before the body runs.
    fn dispose_dynamic(&mut self, resources: Vec<BoundUsingResource>) -> Vec<BoundUsingResource> {
        let mut disposed = Vec::with_capacity(resources.len());
        for resource in resources {
            let declared = self.body.locals[resource.local.0 as usize].ty.clone();
            let disposable = self.framework_type("System.IDisposable");
            let Some(disposable) = disposable.filter(|_| matches!(declared, Type::Dynamic)) else {
                disposed.push(resource);
                continue;
            };
            let span = resource.value.span;
            let read =
                BoundExpression::new(BoundExpressionKind::Local(resource.local), declared, span);
            let converted = self.convert(read, &disposable);
            let held = self.declare_synthetic_local("disposable", disposable.clone());
            let dispose = self.dispose_of(&disposable);
            disposed.push(resource);
            disposed.push(BoundUsingResource {
                local: held,
                value: converted,
                dispose,
                awaited: None,
            });
        }
        disposed
    }

    /// CS1674: what a `using` holds has to be something it can dispose.
    /// Said once per `using`, where Roslyn says it; not of an `await using`,
    /// which disposes another way, nor of a type parameter or `dynamic`,
    /// whose `Dispose` is found another way too.
    fn check_disposable(
        &mut self,
        node: &SyntaxNode,
        resources: &[BoundUsingResource],
        at: TextSpan,
    ) {
        if awaits(node) {
            return;
        }
        let symbols = self.binder.compilation().symbols();
        let undisposable = resources.iter().find(|resource| {
            let declared = &self.body.locals[resource.local.0 as usize].ty;
            resource.dispose.is_none()
                && [declared, &resource.value.ty].iter().all(|ty| {
                    matches!(ty, Type::Named { .. } | Type::Array { .. })
                        && ty
                            .symbol()
                            .is_none_or(|symbol| symbols.get(symbol).kind == SymbolKind::NamedType)
                })
        });
        if let Some(resource) = undisposable {
            let shown = self.display(&self.body.locals[resource.local.0 as usize].ty.clone());
            self.report(ErrorCode::ErrNoConvToIDisp, at, &[&shown]);
        }
    }

    /// The `Dispose` a `using` will call on a resource of this type.
    ///
    /// Anything that converts to `IDisposable` is disposed through it
    /// (§13.14), `((IDisposable)r).Dispose()`: the interface's method,
    /// however the type implements it — a public `Dispose()` beside an
    /// explicit `IDisposable.Dispose()` is not the one called. A `T?` is
    /// disposed as the `T` inside it. What converts to nothing — a `ref
    /// struct`, which can implement nothing — is disposed by the pattern: a
    /// `Dispose()` of its own.
    fn dispose_of(&self, ty: &Type) -> Option<SymbolId> {
        if matches!(ty, Type::Dynamic | Type::Null | Type::Error) {
            return None;
        }
        let disposable = self
            .binder
            .compilation()
            .type_by_metadata_name("System.IDisposable");
        let inside = self
            .binder
            .nullable_underlying(ty)
            .unwrap_or_else(|| ty.clone());
        if let Some(disposable) = disposable
            && self
                .binder
                .converts_implicitly(&inside, &Type::named(disposable))
            && let Some(dispose) = self
                .binder
                .lookup_member(disposable, "Dispose")
                .first()
                .copied()
        {
            return Some(dispose);
        }
        let symbol = ty.symbol()?;
        self.binder
            .lookup_member(symbol, "Dispose")
            .into_iter()
            .find(|candidate| {
                let symbols = self.binder.compilation().symbols();
                symbols.get(*candidate).kind == SymbolKind::Method
                    && symbols
                        .get(*candidate)
                        .as_method()
                        .is_some_and(|method| method.parameters.is_empty())
            })
    }

    fn bind_try_statement(&mut self, node: &SyntaxNode) -> BoundStatementKind {
        let body = node
            .child_of_kind(SyntaxKind::Block)
            .map(|block| Box::new(self.bind_block(&block)));
        let Some(body) = body else {
            return BoundStatementKind::Unsupported(node.kind());
        };

        let mut catches = Vec::new();
        let mut finally = None;
        for child in node.children() {
            match child.kind() {
                SyntaxKind::CatchClause => catches.push(self.bind_catch_clause(&child)),
                SyntaxKind::FinallyClause => {
                    finally = child
                        .child_of_kind(SyntaxKind::Block)
                        .map(|block| Box::new(self.bind_block(&block)));
                }
                _ => {}
            }
        }

        BoundStatementKind::Try {
            body,
            catches,
            finally,
        }
    }

    fn bind_catch_clause(&mut self, node: &SyntaxNode) -> BoundCatch {
        // The exception variable and the filter live for the handler only.
        self.push_scope();
        let declaration = node.child_of_kind(SyntaxKind::CatchDeclaration);
        // A bare `catch` catches everything, which is what `System.Exception`
        // means in metadata.
        let exception_type = declaration
            .as_ref()
            .and_then(|declaration| {
                declaration
                    .children()
                    .find(|child| child.kind().is_type_node())
            })
            .map_or_else(
                || {
                    self.binder
                        .compilation()
                        .type_by_metadata_name("System.Exception")
                        .map_or(Type::Error, Type::named)
                },
                |ty| self.resolve(&ty),
            );

        let local = declaration.as_ref().and_then(|declaration| {
            let token = declaration
                .child_tokens()
                .find(|token| token.kind() == SyntaxKind::IdentifierToken)?;
            Some(self.declare_local(token.value_text(), exception_type.clone(), token.span()))
        });

        let filter = node
            .child_of_kind(SyntaxKind::CatchFilterClause)
            .and_then(|clause| clause.children().find(|child| child.kind().is_expression()))
            .map(|condition| self.bind_condition(Some(&condition)));

        let body = node.child_of_kind(SyntaxKind::Block).map_or_else(
            || BoundStatement::new(BoundStatementKind::Empty, node.span()),
            |block| self.bind_block(&block),
        );
        self.pop_scope();

        BoundCatch {
            exception_type,
            local,
            filter,
            body,
        }
    }
}

/// Whether a `using` statement or declaration is an `await using`.
fn awaits(node: &SyntaxNode) -> bool {
    node.child_tokens()
        .any(|token| token.kind() == SyntaxKind::AwaitKeyword)
}

/// Whether a `fixed` declaration can pin `value` into `declared`.
///
/// A string pins to a `char*` and an array to a pointer to its element; both
/// are conversions that exist nowhere else in the language.
fn pins_to(declared: &Type, value: &Type) -> bool {
    let Type::Pointer(element) = declared else {
        return false;
    };
    // `fixed (void* q = chars)`: the `char*` the array pins to converts to
    // any `void*`, as a string's does.
    if matches!(**element, Type::Void)
        && matches!(value, Type::Array { rank: 1, .. } | Type::Named { .. })
    {
        return true;
    }
    match value {
        Type::Array {
            element: source, ..
        } => source == element,
        Type::Named { .. } => matches!(&**element, Type::Named { .. }),
        // A type parameter pins through a `GetPinnableReference` extension.
        Type::TypeParameter(_) => true,
        _ => false,
    }
}

/// Whether an expression may stand as a statement on its own (§13.7): a
/// call, an assignment, an increment or decrement, an `await`, or making an
/// object — but not making a delegate, which is written the same way, nor a
/// `nameof`, which is written as a call.
fn is_statement_expression(syntax: &SyntaxNode, bound: &BoundExpression) -> bool {
    match syntax.kind() {
        SyntaxKind::InvocationExpression => !matches!(
            bound.kind,
            BoundExpressionKind::Literal(crate::bound::ConstantValue::String(_))
        ),
        SyntaxKind::ObjectCreationExpression => {
            !matches!(bound.kind, BoundExpressionKind::DelegateCreation { .. })
        }
        SyntaxKind::SimpleAssignmentExpression
        | SyntaxKind::AddAssignmentExpression
        | SyntaxKind::SubtractAssignmentExpression
        | SyntaxKind::MultiplyAssignmentExpression
        | SyntaxKind::DivideAssignmentExpression
        | SyntaxKind::ModuloAssignmentExpression
        | SyntaxKind::AndAssignmentExpression
        | SyntaxKind::OrAssignmentExpression
        | SyntaxKind::ExclusiveOrAssignmentExpression
        | SyntaxKind::LeftShiftAssignmentExpression
        | SyntaxKind::RightShiftAssignmentExpression
        | SyntaxKind::UnsignedRightShiftAssignmentExpression
        | SyntaxKind::CoalesceAssignmentExpression
        | SyntaxKind::PostIncrementExpression
        | SyntaxKind::PostDecrementExpression
        | SyntaxKind::PreIncrementExpression
        | SyntaxKind::PreDecrementExpression
        | SyntaxKind::AwaitExpression => true,
        // `a?.M();` is a call where there is something to call it on.
        SyntaxKind::ConditionalAccessExpression => syntax
            .children()
            .last()
            .is_some_and(|access| is_statement_expression(&access, bound)),
        // `(var(x, y) = 44);` is a statement to Roslyn's parser, which reads
        // it as the start of a deconstruction; this one does not, and would
        // otherwise turn a program `csc` accepts into an error.
        SyntaxKind::ParenthesizedExpression => syntax
            .children()
            .next()
            .is_some_and(|inner| is_statement_expression(&inner, bound)),
        // A name the parser had to make up stands for a statement that is
        // not there at all.
        SyntaxKind::IdentifierName => syntax.span().is_empty(),
        _ => false,
    }
}

/// `(a, b) = (b, a);` as a statement: the deconstruction is done for what it
/// does, and the tuple it would be worth is never made.
fn unused_deconstruction(node: &SyntaxNode, value: BoundExpression) -> BoundExpression {
    let deconstructs = node.kind() == SyntaxKind::SimpleAssignmentExpression
        && node.children().next().is_some_and(|target| {
            matches!(
                target.kind(),
                SyntaxKind::TupleExpression | SyntaxKind::DeclarationExpression
            )
        });
    if deconstructs && matches!(value.kind, BoundExpressionKind::Sequence(_)) {
        super::tuples::deconstruction_unused(value)
    } else {
        value
    }
}

/// What a value's syntax is once the parentheses, `checked(...)` and
/// `unchecked(...)` around it are taken off: an expression that is wrapped
/// is bound as the one inside, and an error about its value is reported
/// there.
fn inside_wrappers(node: &SyntaxNode) -> SyntaxNode {
    let mut node = node.clone();
    while matches!(
        node.kind(),
        SyntaxKind::ParenthesizedExpression
            | SyntaxKind::CheckedExpression
            | SyntaxKind::UncheckedExpression
    ) {
        let Some(inner) = node.children().find(|child| child.kind().is_expression()) else {
            break;
        };
        node = inner;
    }
    node
}
