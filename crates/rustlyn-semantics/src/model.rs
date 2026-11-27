//! The semantic model: what a particular piece of syntax means.
//!
//! The declaration table answers questions about the program as a whole. This
//! answers them about one node — what does this name refer to, what type does
//! this expression have — which is what an IDE asks all day long.

use rustlyn_syntax::{SyntaxKind, SyntaxNode};

use crate::binder::{Binder, Context, Diagnostics};
use crate::body::BodyBinder;
use crate::bound::{BoundBody, BoundSymbol};
use crate::compilation::Compilation;
use crate::symbol::{SymbolId, SymbolKind};
use crate::types::Type;

/// Semantic questions about one syntax tree of a compilation.
#[derive(Debug)]
pub struct SemanticModel<'a> {
    binder: Binder<'a>,
    tree: usize,
}

impl<'a> SemanticModel<'a> {
    /// A model for tree `tree` of `compilation`.
    #[must_use]
    pub fn new(compilation: &'a Compilation, tree: usize) -> Self {
        Self {
            binder: Binder::new(compilation),
            tree,
        }
    }

    /// A model of tree `speculation.tree` as edited: its nodes are the new
    /// tree's, and everything else is as compiled.
    #[must_use]
    pub fn speculative(
        compilation: &'a Compilation,
        speculation: crate::binder::Speculation,
    ) -> Self {
        let tree = speculation.tree;
        Self {
            binder: Binder::speculative(compilation, speculation),
            tree,
        }
    }

    #[must_use]
    pub const fn compilation(&self) -> &'a Compilation {
        self.binder.compilation()
    }

    #[must_use]
    pub const fn tree_index(&self) -> usize {
        self.tree
    }

    /// The symbol a declaration node declares.
    #[must_use]
    pub fn declared_symbol(&self, node: &SyntaxNode) -> Option<SymbolId> {
        self.binder.declared_symbol_at(self.tree, node)
    }

    /// The type a piece of type syntax denotes.
    #[must_use]
    pub fn type_of_syntax(&self, node: &SyntaxNode) -> Type {
        let context = self.binder.context_at(self.tree, node);
        let mut sink = Diagnostics::new();
        self.binder.resolve_type(node, &context, &mut sink)
    }

    /// What a name refers to.
    ///
    /// A name in a type position resolves to a type or namespace; elsewhere it
    /// may also be a local, a parameter or a member of the enclosing type.
    #[must_use]
    pub fn symbol_at(&self, node: &SyntaxNode) -> Option<SymbolId> {
        self.symbol_at_with(node, &mut |at| {
            std::sync::Arc::new(self.binder.context_at(self.tree, at))
        })
    }

    /// [`SemanticModel::symbol_at`], with the scopes of a node as `context_of`
    /// has them: a caller that asks about many nodes keeps them, which are
    /// otherwise read off every ancestor of the node each time.
    #[must_use]
    pub fn symbol_at_with(
        &self,
        node: &SyntaxNode,
        context_of: &mut dyn FnMut(&SyntaxNode) -> std::sync::Arc<Context>,
    ) -> Option<SymbolId> {
        // `a.b` — resolve the left side first, then look `b` up inside it.
        if let Some(parent) = node.parent()
            && matches!(
                parent.kind(),
                SyntaxKind::QualifiedName | SyntaxKind::SimpleMemberAccessExpression
            )
            && parent.children().next().as_ref() != Some(node)
        {
            let left = parent.children().next()?;
            let container = self.symbol_at_with(&left, context_of)?;
            let name = identifier_text(node)?;
            // `System.EventHandler<T>` is the generic one, not the
            // `EventHandler` beside it: as many type parameters as written.
            let arity = node
                .child_of_kind(SyntaxKind::TypeArgumentList)
                .map_or(0, |list| {
                    list.children()
                        .filter(|child| child.kind().is_type_node())
                        .count()
                });
            if let Some(ty) = self
                .compilation()
                .symbols()
                .lookup_type(container, &name, arity)
            {
                return Some(ty);
            }
            return self
                .binder
                .lookup_member(container, &name)
                .first()
                .copied()
                .or_else(|| {
                    self.compilation()
                        .symbols()
                        .lookup(container, &name)
                        .first()
                        .copied()
                });
        }

        let context = context_of(node);
        if let Some(symbol) = self.binder.resolve_namespace_or_type(node, &context) {
            return Some(symbol);
        }

        // Not a type: try the members of the enclosing type, then its bases.
        let name = identifier_text(node)?;
        let enclosing = context.enclosing_type()?;
        self.binder.lookup_member(enclosing, &name).first().copied()
    }

    /// The type of what a symbol holds.
    #[must_use]
    pub fn type_of_symbol(&self, symbol: SymbolId) -> Type {
        let mut sink = Diagnostics::new();
        self.binder.type_of(symbol, &mut sink)
    }

    /// The base types and interfaces of a type, resolved.
    #[must_use]
    pub fn base_types_of(&self, symbol: SymbolId) -> Vec<Type> {
        self.binder.base_types_of(symbol)
    }

    /// The type a declaration's name introduces, for a field, parameter, local
    /// or property.
    #[must_use]
    pub fn declared_type(&self, node: &SyntaxNode) -> Type {
        match self.declared_symbol(node) {
            Some(symbol)
                if self.compilation().symbols().get(symbol).kind != SymbolKind::Namespace =>
            {
                self.type_of_symbol(symbol)
            }
            _ => Type::Error,
        }
    }

    #[must_use]
    pub const fn binder(&self) -> &Binder<'a> {
        &self.binder
    }

    /// Binds the body `node` sits in.
    ///
    /// Bodies are bound on demand and not cached, so asking about many nodes
    /// in one body does the work many times. Roslyn caches this per member;
    /// doing the same here is the obvious next step.
    #[must_use]
    pub fn bound_body_containing(&self, node: &SyntaxNode) -> Option<BoundBody> {
        let owner = Self::body_owner(node)?;
        Some(self.bind_body(&owner))
    }

    /// The member whose body `node` is in: the unit that is bound in one go,
    /// and so the unit worth keeping a bound body for when asking about many
    /// nodes of it.
    #[must_use]
    pub fn body_owner(node: &SyntaxNode) -> Option<SyntaxNode> {
        let mut declarator = None;
        for ancestor in std::iter::once(node.clone()).chain(node.ancestors()) {
            match ancestor.kind() {
                // A field's initializer belongs to its declarator: `int a = 1,
                // b = 2;` is two bodies, and the declaration holds neither.
                SyntaxKind::VariableDeclarator => declarator = Some(ancestor),
                SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration => {
                    return declarator.or(Some(ancestor));
                }
                kind if is_body_owner(kind) => return Some(ancestor),
                _ => {}
            }
        }
        None
    }

    /// Binds the body of `owner`, one of what [`Self::body_owner`] returns.
    #[must_use]
    pub fn bind_body(&self, owner: &SyntaxNode) -> BoundBody {
        crate::parallel::deep(|| BodyBinder::bind_member(&self.binder, self.tree, owner))
    }

    /// [`Self::bind_body`] for an editor: the lambdas of calls that do not
    /// resolve are bound too, so that what is inside them can be asked
    /// about. Not for compiling.
    #[must_use]
    pub fn bind_body_for_editor(&self, owner: &SyntaxNode) -> BoundBody {
        crate::parallel::deep(|| BodyBinder::bind_member_for_editor(&self.binder, self.tree, owner))
    }

    /// The arguments of the attribute `attribute` bound for an editor: what
    /// each name in them refers to. The attribute is bound where it is
    /// written, in the declaration it is on.
    #[must_use]
    pub fn bind_attribute_for_editor(&self, attribute: &SyntaxNode) -> BoundBody {
        let declaration = attribute
            .parent()
            .and_then(|list| list.parent().cloned())
            .unwrap_or_else(|| attribute.clone());
        crate::parallel::deep(|| {
            BodyBinder::bind_attribute_for_editor(&self.binder, self.tree, &declaration, attribute)
        })
    }

    /// A value outside any body bound for an editor: a parameter's default,
    /// in the member the parameter is of, an enum member's value, a fixed
    /// buffer's size.
    #[must_use]
    pub fn bind_default_for_editor(&self, value: &SyntaxNode) -> BoundBody {
        let declaration = value
            .ancestors()
            .find(|node| {
                !matches!(
                    node.kind(),
                    SyntaxKind::EqualsValueClause
                        | SyntaxKind::Parameter
                        | SyntaxKind::ParameterList
                        | SyntaxKind::BracketedParameterList
                )
            })
            .unwrap_or_else(|| value.clone());
        crate::parallel::deep(|| {
            BodyBinder::bind_default_for_editor(&self.binder, self.tree, &declaration, value)
        })
    }

    /// The type of an expression.
    #[must_use]
    pub fn type_of(&self, node: &SyntaxNode) -> Type {
        if node.kind().is_type_node() && !is_expression_name(node) {
            return self.type_of_syntax(node);
        }
        self.bound_body_containing(node)
            .and_then(|body| body.type_at(node.span()).cloned())
            .unwrap_or(Type::Error)
    }

    /// What a name inside a body refers to.
    #[must_use]
    pub fn referenced_symbol(&self, node: &SyntaxNode) -> Option<BoundSymbol> {
        self.bound_body_containing(node)?.reference_at(node.span())
    }

    /// Everything the bodies of this file report.
    #[must_use]
    pub fn body_diagnostics(&self) -> Diagnostics {
        crate::parallel::deep(|| self.body_diagnostics_here())
    }

    fn body_diagnostics_here(&self) -> Diagnostics {
        let root = self.compilation().trees()[self.tree].root();
        let mut diagnostics = Diagnostics::new();
        for node in root.descendants() {
            if node.kind() == SyntaxKind::FieldDeclaration
                || node.kind() == SyntaxKind::EventFieldDeclaration
            {
                // A field's initializer is its declarator's, one per name:
                // `int a = 1, b = a;` is two of them. Only the field's own: a
                // local declared in a lambda of the initializer is bound
                // with the lambda, where its parameters are in scope.
                for declarator in node
                    .child_of_kind(SyntaxKind::VariableDeclaration)
                    .into_iter()
                    .flat_map(|declaration| declaration.children())
                    .filter(|declarator| declarator.kind() == SyntaxKind::VariableDeclarator)
                    .filter(|declarator| {
                        declarator
                            .child_of_kind(SyntaxKind::EqualsValueClause)
                            .is_some()
                    })
                {
                    diagnostics.extend(
                        BodyBinder::bind_member(&self.binder, self.tree, &declarator).diagnostics,
                    );
                }
            } else if is_body_owner(node.kind()) && node.kind() != SyntaxKind::CompilationUnit {
                diagnostics
                    .extend(BodyBinder::bind_member(&self.binder, self.tree, &node).diagnostics);
            }
        }
        // Top-level statements belong to the file rather than to any member.
        if root
            .children()
            .any(|child| child.kind() == SyntaxKind::GlobalStatement)
        {
            diagnostics.extend(BodyBinder::bind_member(&self.binder, self.tree, &root).diagnostics);
        }
        diagnostics
    }
}

/// Whether a node is the kind that owns a body.
#[must_use]
pub const fn is_body_owner(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::MethodDeclaration
            | SyntaxKind::GetAccessorDeclaration
            | SyntaxKind::SetAccessorDeclaration
            | SyntaxKind::InitAccessorDeclaration
            | SyntaxKind::AddAccessorDeclaration
            | SyntaxKind::RemoveAccessorDeclaration
            | SyntaxKind::ConstructorDeclaration
            | SyntaxKind::DestructorDeclaration
            | SyntaxKind::OperatorDeclaration
            | SyntaxKind::ConversionOperatorDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::IndexerDeclaration
            | SyntaxKind::EventDeclaration
            | SyntaxKind::FieldDeclaration
            | SyntaxKind::CompilationUnit
    )
}

/// Whether a name node is being used as an expression rather than as a type.
fn is_expression_name(node: &SyntaxNode) -> bool {
    node.parent().is_some_and(|parent| {
        parent.kind().is_expression_node() || parent.kind() == SyntaxKind::Argument
    })
}

fn identifier_text(node: &SyntaxNode) -> Option<String> {
    node.child_tokens()
        .find(|token| token.kind() == SyntaxKind::IdentifierToken)
        .map(|token| token.value_text().to_string())
}
