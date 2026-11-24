//! What an editor shows beside the code rather than jumps to: the errors in
//! a file, the signature of the call being typed, the documentation of a
//! name.
//!
//! Each works on the file as the editor has it, through the same
//! [`View`] the jumps use: an unsaved edit is parsed again and bound against
//! the compilation as it is.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};

use rustlyn_diagnostics::Diagnostic;
use rustlyn_semantics::{MethodKind, SymbolId, SymbolKind, Type, is_body_owner};
use rustlyn_syntax::{SyntaxKind, SyntaxNode, SyntaxToken, parse_with};
use rustlyn_text::SourceText;

use super::{Resolved, Semantic, View, describe_symbol};

/// The overloads of the call being typed, and where in it the cursor is.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Signatures {
    pub items: Vec<Signature>,
    /// Which of `items` the arguments so far fit best.
    pub active: usize,
    /// Which parameter the cursor is at.
    pub parameter: usize,
}

/// One overload: `void Add(T item)`, with where each parameter is in it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Signature {
    pub label: String,
    /// Byte ranges of `label`, one per parameter.
    pub parameters: Vec<(u32, u32)>,
}

/// What the documentation comment of a name says, as plain text.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Documentation {
    /// `void Add(T item)`.
    pub signature: String,
    /// Where it is declared: `System.Collections.Generic.List<T>`.
    pub container: String,
    pub summary: String,
    pub parameters: Vec<(String, String)>,
    pub returns: String,
}

impl Semantic {
    // MARK: - diagnostics

    /// What is wrong with `path` as it reads now: its syntax errors, what
    /// declaring its types and members reported, and what binding each of
    /// its bodies finds. Sorted by place.
    #[must_use]
    pub fn diagnostics(&self, path: &Path, text: Option<&str>) -> Option<Vec<Diagnostic>> {
        let tree = self.tree_index(path)?;
        let compiled_syntax: Vec<Diagnostic> =
            self.compilation.trees().get(tree)?.diagnostics().to_vec();
        let mut view = self.view_of(path, text)?;
        let mut found: Vec<Diagnostic> = Vec::new();

        match (&view.speculation, text) {
            (Some(_), Some(text)) => {
                let edited = parse_with(
                    SourceText::new(path.to_string_lossy(), text),
                    &self.parse_options_of(path),
                );
                found.extend(edited.diagnostics().iter().cloned());
            }
            _ => found.extend(compiled_syntax.iter().cloned()),
        }
        // What the declarations report — those not about the syntax, which
        // is already in — carried over to the edited text where the edit did
        // not touch them.
        // The signatures, base lists and attributes of the file, and what its
        // types get wrong against what they inherit, come with them.
        let declared = self
            .compilation
            .diagnostics()
            .iter()
            .filter(|entry| entry.tree == tree && !compiled_syntax.contains(&entry.diagnostic))
            .map(|entry| entry.diagnostic.clone())
            .chain(self.compilation.declaration_diagnostics(tree));
        for diagnostic in declared {
            match &view.speculation {
                Some(speculation) => {
                    if let Some(span) = speculation.unmap(diagnostic.span()) {
                        found.push(diagnostic.with_span(span));
                    }
                }
                None => found.push(diagnostic),
            }
        }
        // Two projects' types of one name are one type to a compilation of
        // both, and its members each other's duplicates: to either project
        // they are not.
        found.retain(|diagnostic| !self.duplicate_across_projects(&view, tree, diagnostic));
        found.extend(view.body_diagnostics());
        // A warning the file switched off with `#pragma warning disable`,
        // or its project with `-nowarn:`, `<NoWarn>` or a warning level of 0.
        let pragmas = rustlyn_semantics::WarningState::of(&view.root);
        found.retain(|diagnostic| !pragmas.is_suppressed(diagnostic));
        found.retain(|diagnostic| {
            diagnostic.severity() != rustlyn_diagnostics::Severity::Warning
                || self.reports_warning(tree, u32::from(diagnostic.code().number()))
        });

        found.sort_by_key(|diagnostic| (diagnostic.span().start(), diagnostic.span().end()));
        found.dedup_by(|a, b| a.span() == b.span() && a.code() == b.code());
        Some(found)
    }

    /// Whether the project file `tree` is of reports warning `code`: Unity
    /// builds its packages with `-warn:0`, and the rest without CS0169 and
    /// CS0649.
    pub(crate) fn reports_warning(&self, tree: usize, code: u32) -> bool {
        let owner = usize::from(self.compilation.tree_assembly(tree));
        self.project
            .assembly_warnings
            .get(owner)
            .is_none_or(|warnings| warnings.reports(code))
    }

    fn duplicate_across_projects(
        &self,
        view: &View<'_>,
        tree: usize,
        diagnostic: &Diagnostic,
    ) -> bool {
        if !matches!(diagnostic.code().number(), 101 | 102 | 111) {
            return false;
        }
        // The span may start at a modifier: `public Option Option { get; }`.
        let Some(token) = view.root.find_token(diagnostic.span().start()) else {
            return false;
        };
        std::iter::once(token.parent().clone())
            .chain(token.parent().ancestors())
            .find(|node| {
                matches!(
                    node.kind(),
                    SyntaxKind::ClassDeclaration
                        | SyntaxKind::StructDeclaration
                        | SyntaxKind::InterfaceDeclaration
                        | SyntaxKind::RecordDeclaration
                        | SyntaxKind::RecordStructDeclaration
                        | SyntaxKind::EnumDeclaration
                        | SyntaxKind::DelegateDeclaration
                )
            })
            .and_then(|node| self.compilation.declared_symbol(tree, node.span()))
            .is_some_and(|ty| self.compilation.declared_in_several_assemblies(ty))
    }

    // MARK: - signatures

    /// The overloads of the call whose argument list holds `offset`.
    #[must_use]
    pub fn signatures(&self, path: &Path, offset: u32, text: Option<&str>) -> Option<Signatures> {
        let mut view = self.view_of(path, text)?;
        view.signatures(offset)
    }

    // MARK: - documentation

    /// The documentation of the name at `offset`: its `///` comment when it
    /// is declared in the project, the assembly's XML file when it comes
    /// from one.
    #[must_use]
    pub fn documentation(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
    ) -> Option<Documentation> {
        let mut view = self.view_of(path, text)?;
        let token = view.name_token_at(offset)?;
        // `var` is the type it stands for, as constructed:
        // `Dictionary<string, int>`, not `Dictionary<TKey, TValue>`.
        let var = view.var_type(&token);
        let resolved = view.resolve(&token)?;
        let Resolved::Symbol(symbol) = resolved else {
            return Some(Documentation {
                signature: self.describe(&resolved),
                ..Documentation::default()
            });
        };
        // What the type parameters stand for at this use: the receiver's
        // type arguments, those the call inferred.
        let arguments: HashMap<SymbolId, Type> = match &var {
            Some(Type::Named {
                symbol: named,
                type_arguments,
            }) if *named == symbol => self
                .compilation
                .symbols()
                .get(symbol)
                .as_named_type()
                .map(|detail| {
                    detail
                        .type_parameters
                        .iter()
                        .copied()
                        .zip(type_arguments.iter().cloned())
                        .collect()
                })
                .unwrap_or_default(),
            _ => view.type_arguments_at(symbol, &token).into_iter().collect(),
        };
        let signature = super::describe_symbol_in(&self.compilation, symbol, &arguments);
        let symbols = self.compilation.symbols();
        let container = symbols
            .get(symbol)
            .container
            .filter(|container| !symbols.get(*container).name.is_empty())
            .map(|container| container_name(&self.compilation, container, &arguments))
            .unwrap_or_default();
        let xml = if self.compilation.is_from_metadata(symbol) {
            self.metadata_documentation(symbol)
        } else {
            self.source_documentation(symbol)
        };
        let mut documentation = xml.map(|xml| parse_documentation(&xml)).unwrap_or_default();
        documentation.signature = signature;
        documentation.container = container;
        Some(documentation)
    }

    /// The `///` lines above a symbol's first declaration, without the
    /// slashes.
    pub(super) fn source_documentation(&self, symbol: SymbolId) -> Option<String> {
        let symbols = self.compilation.symbols();
        let location = symbols.get(symbol).locations.first()?;
        let tree = self.compilation.trees().get(location.tree)?;
        let root = tree.root();
        let token = root.find_token(location.span.start())?;
        // The declaration the name belongs to: the comment is in front of
        // its first token, its attributes and modifiers included.
        let parent = token.parent();
        let declaration = std::iter::once(parent.clone())
            .chain(parent.ancestors())
            .find(|node| is_declaration(node.kind()))?;
        let first = declaration.first_token()?;
        let mut lines = Vec::new();
        for trivia in first.leading_trivia() {
            match trivia.kind() {
                SyntaxKind::SingleLineDocumentationCommentTrivia => {
                    for line in trivia.text().lines() {
                        let line = line.trim_start();
                        let line = line.strip_prefix("///").unwrap_or(line);
                        lines.push(line.strip_prefix(' ').unwrap_or(line).to_string());
                    }
                }
                SyntaxKind::MultiLineDocumentationCommentTrivia => {
                    let body = trivia
                        .text()
                        .trim_start_matches("/**")
                        .trim_end_matches("*/");
                    for line in body.lines() {
                        let line = line.trim_start();
                        lines.push(
                            line.strip_prefix('*')
                                .unwrap_or(line)
                                .trim_start()
                                .to_string(),
                        );
                    }
                }
                _ => {}
            }
        }
        (!lines.is_empty()).then(|| lines.join("\n"))
    }

    /// The `<member>` for a symbol in the XML file beside its assembly.
    pub(super) fn metadata_documentation(&self, symbol: SymbolId) -> Option<String> {
        let symbols = self.compilation.symbols();
        let reference = self.compilation.assembly_of(symbol)?;
        let assembly = self.assemblies.get(&reference.name.to_ascii_lowercase())?;
        let docs = xml_documentation(&assembly.with_extension("xml"))?;
        let found = symbols.get(symbol);
        let owner = |id: SymbolId| symbols.metadata_qualified_name(id).replace('+', ".");
        match found.kind {
            SymbolKind::NamedType => docs.get(&format!("T:{}", owner(symbol))),
            SymbolKind::Field => docs.get(&format!("F:{}", owner(symbol))),
            SymbolKind::Property => docs.get(&format!("P:{}", owner(symbol))),
            SymbolKind::Event => docs.get(&format!("E:{}", owner(symbol))),
            SymbolKind::Method => {
                let method = found.as_method()?;
                let container = owner(found.container?);
                let name = match method.method_kind {
                    MethodKind::Constructor => "#ctor".to_string(),
                    MethodKind::StaticConstructor => "#cctor".to_string(),
                    _ => found.metadata_name(),
                };
                // Parameter types spelled the way the XML file does are a
                // grammar of their own; the count picks the overload well
                // enough.
                docs.method(&format!("M:{container}.{name}"), method.parameters.len())
            }
            _ => None,
        }
    }
}

impl View<'_> {
    /// What binding every body of the file reports — the same bodies
    /// [`SemanticModel::body_diagnostics`](rustlyn_semantics::SemanticModel::body_diagnostics)
    /// binds, through the view's cache.
    fn body_diagnostics(&mut self) -> Vec<Diagnostic> {
        // A field's initializer is its declarator's body, one per name, as
        // the compiler binds it: `int a = 1, b = a;` is two of them. Asked
        // of the declaration, it was none, and nothing wrong in an
        // initializer reached the editor.
        let mut owners: Vec<SyntaxNode> = Vec::new();
        for node in self.root.descendants() {
            match node.kind() {
                SyntaxKind::FieldDeclaration | SyntaxKind::EventFieldDeclaration => owners.extend(
                    node.child_of_kind(SyntaxKind::VariableDeclaration)
                        .into_iter()
                        .flat_map(|declaration| declaration.children())
                        .filter(|declarator| {
                            declarator.kind() == SyntaxKind::VariableDeclarator
                                && declarator
                                    .child_of_kind(SyntaxKind::EqualsValueClause)
                                    .is_some()
                        }),
                ),
                kind if is_body_owner(kind) && kind != SyntaxKind::CompilationUnit => {
                    owners.push(node.clone());
                }
                _ => {}
            }
        }
        // Top-level statements belong to the file rather than to any member.
        if self
            .root
            .children()
            .any(|child| child.kind() == SyntaxKind::GlobalStatement)
        {
            owners.push(self.root.clone());
        }
        let mut found = Vec::new();
        for owner in owners {
            if let Some(body) = self.body_for(&owner) {
                let tree = self.tree;
                found.extend(
                    body.diagnostics
                        .iter()
                        .filter(|(at, _)| *at == tree)
                        .map(|(_, diagnostic)| diagnostic.clone()),
                );
            }
        }
        found
    }

    /// The overloads of the call whose argument list holds `offset`.
    pub fn signatures(&mut self, offset: u32) -> Option<Signatures> {
        let token = self
            .root
            .find_token(offset.checked_sub(1)?)
            .or_else(|| self.root.find_token(offset))?;
        let parent = token.parent();
        let list = std::iter::once(parent.clone())
            .chain(parent.ancestors())
            .find(|node| {
                node.kind() == SyntaxKind::ArgumentList && inside_parentheses(node, offset)
            })?;
        let call = list.parent()?.clone();

        // Which argument the cursor is in, and its name when it has one.
        let commas = list
            .child_tokens()
            .filter(|comma| comma.kind() == SyntaxKind::CommaToken && comma.span().end() <= offset)
            .count();
        let named = list
            .children()
            .filter(|argument| argument.kind() == SyntaxKind::Argument)
            .find(|argument| argument.span().start() <= offset && offset <= argument.span().end())
            .and_then(|argument| argument.child_of_kind(SyntaxKind::NameColon))
            .and_then(|colon| {
                colon
                    .descendant_tokens()
                    .find(|t| t.kind() == SyntaxKind::IdentifierToken)
            })
            .map(|name| name.value_text().to_string());

        let symbols = self.compilation().symbols();
        let (candidates, chosen, shift) = match call.kind() {
            SyntaxKind::InvocationExpression => {
                let callee = call.children().next()?;
                let name = name_token(&callee)?;
                let chosen = match self.resolve(&name) {
                    Some(Resolved::Symbol(symbol))
                        if symbols.get(symbol).kind == SymbolKind::Method =>
                    {
                        Some(symbol)
                    }
                    _ => None,
                };
                let candidates = match chosen {
                    Some(method) => overloads(self.compilation(), method),
                    None if callee.kind() == SyntaxKind::SimpleMemberAccessExpression => {
                        self.methods_of_receiver(&callee, name.value_text())
                    }
                    None => self.methods_in_scope(&call, name.value_text()),
                };
                // `list.Where(…)` fills an extension's first parameter with
                // the receiver; `Enumerable.Where(list, …)` does not.
                let receiver_form = callee.kind() == SyntaxKind::SimpleMemberAccessExpression
                    && !callee
                        .children()
                        .next()
                        .and_then(|receiver| name_token(&receiver))
                        .and_then(|token| self.resolve(&token))
                        .is_some_and(|resolved| match resolved {
                            Resolved::Symbol(symbol) => {
                                symbols.get(symbol).kind == SymbolKind::NamedType
                            }
                            Resolved::Local { .. } => false,
                        });
                (candidates, chosen, usize::from(receiver_form))
            }
            SyntaxKind::ObjectCreationExpression => {
                let ty = call
                    .children()
                    .find(|node| node.kind().is_type_node() || is_name(node.kind()))?;
                let name = name_token(&ty)?;
                let ty = match self.resolve(&name)? {
                    Resolved::Symbol(symbol) => {
                        let found = symbols.get(symbol);
                        if found.kind == SymbolKind::Method {
                            found.container?
                        } else {
                            symbol
                        }
                    }
                    Resolved::Local { .. } => return None,
                };
                (constructors(self.compilation(), ty), None, 0)
            }
            SyntaxKind::BaseConstructorInitializer | SyntaxKind::ThisConstructorInitializer => {
                let keyword = call.child_tokens().find(|t| {
                    matches!(t.kind(), SyntaxKind::BaseKeyword | SyntaxKind::ThisKeyword)
                })?;
                match self.resolve(&keyword)? {
                    Resolved::Symbol(symbol) => {
                        let found = symbols.get(symbol);
                        let ty = if found.kind == SymbolKind::Method {
                            found.container?
                        } else {
                            symbol
                        };
                        (constructors(self.compilation(), ty), Some(symbol), 0)
                    }
                    Resolved::Local { .. } => return None,
                }
            }
            _ => return None,
        };
        if candidates.is_empty() {
            return None;
        }

        let items: Vec<Signature> = candidates
            .iter()
            .map(|&method| signature(self.semantic, method))
            .collect();
        let parameter_names = |method: SymbolId| -> Vec<String> {
            symbols
                .get(method)
                .as_method()
                .map(|m| {
                    m.parameters
                        .iter()
                        .map(|p| symbols.get(*p).name.clone())
                        .collect()
                })
                .unwrap_or_default()
        };
        let is_extension = |method: SymbolId| {
            symbols
                .get(method)
                .as_method()
                .is_some_and(|m| m.is_extension)
        };
        let position = |method: SymbolId| -> Option<usize> {
            let names = parameter_names(method);
            if let Some(named) = &named {
                return names.iter().position(|name| name == named);
            }
            let index = commas + if is_extension(method) { shift } else { 0 };
            let params = symbols
                .get(method)
                .as_method()
                .and_then(|m| m.parameters.last())
                .is_some_and(|last| {
                    symbols
                        .get(*last)
                        .as_parameter()
                        .is_some_and(|p| p.is_params)
                });
            if index < names.len() {
                Some(index)
            } else if params && !names.is_empty() {
                Some(names.len() - 1)
            } else {
                None
            }
        };
        let active = chosen
            .and_then(|chosen| candidates.iter().position(|&c| c == chosen))
            .filter(|&index| position(candidates[index]).is_some())
            .or_else(|| candidates.iter().position(|&c| position(c).is_some()))
            .unwrap_or(0);
        let parameter = position(candidates[active]).unwrap_or(commas);
        Some(Signatures {
            items,
            active,
            parameter,
        })
    }

    /// Methods called `name` on what is left of the dot: the type's static
    /// ones when it names a type, the value's type's and its bases' when it
    /// is a value.
    fn methods_of_receiver(&mut self, access: &SyntaxNode, name: &str) -> Vec<SymbolId> {
        let Some(receiver) = access.children().next() else {
            return Vec::new();
        };
        let symbols = self.compilation().symbols();
        let types: Vec<SymbolId> = match self.named(&receiver) {
            Some(symbol) if symbols.get(symbol).kind == SymbolKind::NamedType => vec![symbol],
            _ => {
                let ty = self.type_of(&receiver);
                let mut all: Vec<SymbolId> = self.types_of(&ty).into_iter().collect();
                all.sort_by_key(|id| id.index());
                all
            }
        };
        let mut found: Vec<SymbolId> = Vec::new();
        let mut labels: Vec<String> = Vec::new();
        for ty in types {
            for &member in symbols.lookup(ty, name) {
                if symbols.get(member).kind != SymbolKind::Method {
                    continue;
                }
                let label = describe_symbol(self.compilation(), member);
                if !labels.contains(&label) {
                    labels.push(label);
                    found.push(member);
                }
            }
        }
        found
    }

    /// Methods called `name` visible from `node` without a receiver: the
    /// enclosing types' and their bases'. What is offered when the call does
    /// not bind yet, as it does not while its arguments are being typed.
    fn methods_in_scope(&self, node: &SyntaxNode, name: &str) -> Vec<SymbolId> {
        let symbols = self.compilation().symbols();
        let mut found = Vec::new();
        for ancestor in node.ancestors() {
            if !is_type_declaration(ancestor.kind()) {
                continue;
            }
            let Some(ty) = self.model.declared_symbol(&ancestor) else {
                continue;
            };
            for &member in symbols.lookup(ty, name) {
                if symbols.get(member).kind == SymbolKind::Method && !found.contains(&member) {
                    found.push(member);
                }
            }
        }
        found
    }
}

/// Whether `offset` is between an argument list's parentheses. An unclosed
/// list runs to wherever its missing `)` was put.
fn inside_parentheses(list: &SyntaxNode, offset: u32) -> bool {
    let open = list.child_token_of_kind(SyntaxKind::OpenParenToken);
    let close = list.child_token_of_kind(SyntaxKind::CloseParenToken);
    let after_open = open.is_some_and(|open| !open.is_missing() && open.span().end() <= offset);
    let before_close =
        close.is_none_or(|close| close.is_missing() || offset <= close.span().start());
    after_open && before_close
}

const fn is_name(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::IdentifierName
            | SyntaxKind::GenericName
            | SyntaxKind::QualifiedName
            | SyntaxKind::AliasQualifiedName
    )
}

/// The identifier that names what an expression or a type refers to: `Add`
/// in `list.Add`, `List` in `List<int>`, `Dictionary` in
/// `System.Collections.Generic.Dictionary<K, V>`.
fn name_token(node: &SyntaxNode) -> Option<SyntaxToken> {
    match node.kind() {
        SyntaxKind::IdentifierName | SyntaxKind::GenericName => node
            .child_tokens()
            .find(|t| t.kind() == SyntaxKind::IdentifierToken),
        SyntaxKind::SimpleMemberAccessExpression
        | SyntaxKind::PointerMemberAccessExpression
        | SyntaxKind::MemberBindingExpression
        | SyntaxKind::QualifiedName
        | SyntaxKind::AliasQualifiedName => name_token(&node.children().last()?),
        SyntaxKind::ThisExpression | SyntaxKind::BaseExpression => node.child_tokens().next(),
        _ => None,
    }
}

const fn is_type_declaration(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::ClassDeclaration
            | SyntaxKind::StructDeclaration
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::RecordDeclaration
            | SyntaxKind::RecordStructDeclaration
    )
}

/// Whether a node declares something a documentation comment can be on.
fn is_declaration(kind: SyntaxKind) -> bool {
    is_type_declaration(kind)
        || matches!(
            kind,
            SyntaxKind::EnumDeclaration
                | SyntaxKind::DelegateDeclaration
                | SyntaxKind::EnumMemberDeclaration
                | SyntaxKind::MethodDeclaration
                | SyntaxKind::ConstructorDeclaration
                | SyntaxKind::DestructorDeclaration
                | SyntaxKind::OperatorDeclaration
                | SyntaxKind::ConversionOperatorDeclaration
                | SyntaxKind::PropertyDeclaration
                | SyntaxKind::IndexerDeclaration
                | SyntaxKind::EventDeclaration
                | SyntaxKind::EventFieldDeclaration
                | SyntaxKind::FieldDeclaration
                | SyntaxKind::Parameter
        )
}

/// A method's overloads: everything its type and the types it derives from
/// declare under the same name, the same signature once.
fn overloads(compilation: &rustlyn_semantics::Compilation, method: SymbolId) -> Vec<SymbolId> {
    let symbols = compilation.symbols();
    let found = symbols.get(method);
    let Some(container) = found.container else {
        return vec![method];
    };
    let mut result = vec![method];
    let mut seen = vec![describe_symbol(compilation, method)];
    for &other in symbols.lookup(container, &found.name) {
        if other == method || symbols.get(other).kind != SymbolKind::Method {
            continue;
        }
        let label = describe_symbol(compilation, other);
        if !seen.contains(&label) {
            seen.push(label);
            result.push(other);
        }
    }
    // In declaration order, so the list does not reshuffle as the chosen
    // overload changes while typing.
    result.sort_by_key(|id| id.index());
    result
}

fn constructors(compilation: &rustlyn_semantics::Compilation, ty: SymbolId) -> Vec<SymbolId> {
    let symbols = compilation.symbols();
    let mut found: Vec<SymbolId> = symbols
        .get(ty)
        .members
        .iter()
        .copied()
        .filter(|&member| {
            symbols
                .get(member)
                .as_method()
                .is_some_and(|method| method.method_kind == MethodKind::Constructor)
        })
        .collect();
    found.sort_by_key(|id| id.index());
    found
}

/// A method as a line of text, with where each parameter is in it.
fn signature(semantic: &Semantic, method: SymbolId) -> Signature {
    let compilation = &semantic.compilation;
    let label = describe_symbol(compilation, method);
    let symbols = compilation.symbols();
    let model = rustlyn_semantics::SemanticModel::new(compilation, 0);
    let parts: Vec<String> = symbols
        .get(method)
        .as_method()
        .map(|m| {
            m.parameters
                .iter()
                .map(|&parameter| {
                    let ty = model.type_of_symbol(parameter).display(symbols);
                    format!("{ty} {}", symbols.get(parameter).name)
                })
                .collect()
        })
        .unwrap_or_default();
    // The label ends `(…parameters…)`, joined as `describe_symbol` joins them.
    let joined = parts.join(", ");
    let mut parameters = Vec::with_capacity(parts.len());
    if label.ends_with(')') && label.len() > joined.len() {
        let mut at = label.len() - 1 - joined.len();
        if label[at..label.len() - 1] == joined {
            for part in &parts {
                parameters.push((at as u32, (at + part.len()) as u32));
                at += part.len() + 2;
            }
        }
    }
    Signature { label, parameters }
}

// MARK: - XML documentation

/// An assembly's documentation file: each member's XML by its ID.
struct XmlDocs {
    members: HashMap<String, String>,
}

impl XmlDocs {
    fn get(&self, id: &str) -> Option<String> {
        self.members.get(id).cloned()
    }

    /// A method's documentation by its name and parameter count: `M:T.Add`
    /// with no parameters, `M:T.Add(System.Int32)` with one.
    fn method(&self, prefix: &str, parameters: usize) -> Option<String> {
        if parameters == 0 {
            return self.get(prefix);
        }
        let open = format!("{prefix}(");
        let mut candidates: Vec<(&String, &String)> = self
            .members
            .iter()
            .filter(|(id, _)| id.starts_with(&open))
            .collect();
        candidates.sort_by(|a, b| a.0.cmp(b.0));
        candidates
            .iter()
            .find(|(id, _)| count_parameters(&id[open.len()..]) == parameters)
            .or_else(|| candidates.first())
            .map(|(_, xml)| (*xml).clone())
    }
}

/// How many parameters a documentation ID lists: top-level commas plus one.
fn count_parameters(list: &str) -> usize {
    let mut depth = 0i32;
    let mut count = 1;
    for c in list.chars() {
        match c {
            '(' | '{' | '[' => depth += 1,
            ')' | '}' | ']' => {
                if depth == 0 {
                    break;
                }
                depth -= 1;
            }
            ',' if depth == 0 => count += 1,
            _ => {}
        }
    }
    count
}

/// Documentation files read so far. Several megabytes each, and the same
/// one is asked about again and again.
fn xml_documentation(path: &Path) -> Option<Arc<XmlDocs>> {
    static READ: OnceLock<Mutex<HashMap<PathBuf, Option<Arc<XmlDocs>>>>> = OnceLock::new();
    let read = READ.get_or_init(|| Mutex::new(HashMap::new()));
    if let Some(docs) = read
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .get(path)
    {
        return docs.clone();
    }
    let docs = std::fs::read_to_string(path)
        .ok()
        .map(|text| Arc::new(parse_xml_members(&text)));
    read.lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .insert(path.to_path_buf(), docs.clone());
    docs
}

/// Each `<member name="…">…</member>` of a documentation file.
fn parse_xml_members(text: &str) -> XmlDocs {
    let mut members = HashMap::new();
    let mut rest = text;
    while let Some(start) = rest.find("<member name=\"") {
        rest = &rest[start + "<member name=\"".len()..];
        let Some(quote) = rest.find('"') else { break };
        let id = decode_entities(&rest[..quote]);
        rest = &rest[quote..];
        let Some(open_end) = rest.find('>') else {
            break;
        };
        if rest[..open_end].ends_with('/') {
            rest = &rest[open_end + 1..];
            continue;
        }
        rest = &rest[open_end + 1..];
        let Some(end) = rest.find("</member>") else {
            break;
        };
        members.insert(id, rest[..end].to_string());
        rest = &rest[end..];
    }
    XmlDocs { members }
}

/// Plain text out of a documentation comment's XML.
#[must_use]
pub fn parse_documentation(xml: &str) -> Documentation {
    let mut documentation = Documentation::default();
    if let Some(summary) = element(xml, "summary") {
        documentation.summary = plain(summary);
    } else if !xml.contains('<') {
        documentation.summary = plain(xml);
    }
    if let Some(returns) = element(xml, "returns") {
        documentation.returns = plain(returns);
    }
    let mut rest = xml;
    while let Some(start) = rest.find("<param name=\"") {
        rest = &rest[start + "<param name=\"".len()..];
        let Some(quote) = rest.find('"') else { break };
        let name = rest[..quote].to_string();
        let Some(open_end) = rest.find('>') else {
            break;
        };
        let body = &rest[open_end + 1..];
        let Some(end) = body.find("</param>") else {
            break;
        };
        documentation.parameters.push((name, plain(&body[..end])));
        rest = &body[end..];
    }
    documentation
}

/// The inside of the first `<tag>…</tag>`.
pub(super) fn element<'a>(xml: &'a str, tag: &str) -> Option<&'a str> {
    let open = xml.find(&format!("<{tag}"))?;
    let after = &xml[open..];
    let body_start = after.find('>')? + 1;
    let close = after.find(&format!("</{tag}>"))?;
    (close >= body_start).then(|| &after[body_start..close])
}

/// Tags out, references kept as the names they point to, whitespace folded
/// except for paragraph breaks.
pub(super) fn plain(xml: &str) -> String {
    let mut out = String::with_capacity(xml.len());
    let mut rest = xml;
    while let Some(lt) = rest.find('<') {
        out.push_str(&rest[..lt]);
        let Some(gt) = rest[lt..].find('>') else {
            rest = &rest[lt..];
            break;
        };
        let tag = &rest[lt + 1..lt + gt];
        let name = tag
            .split_whitespace()
            .next()
            .unwrap_or("")
            .trim_end_matches('/');
        match name {
            "see" | "seealso" | "paramref" | "typeparamref" => {
                let attribute = ["cref=\"", "name=\"", "langword=\""]
                    .iter()
                    .find_map(|key| tag.find(key).map(|at| &tag[at + key.len()..]))
                    .and_then(|value| value.split('"').next())
                    .unwrap_or("");
                // `T:System.String` reads as `String`; a generic's arity
                // marker and a method's parameters go too.
                let shown = attribute
                    .split_once(':')
                    .map_or(attribute, |(_, name)| name);
                let shown = shown.split('(').next().unwrap_or(shown);
                let shown = shown.rsplit('.').next().unwrap_or(shown);
                let shown = shown.split('`').next().unwrap_or(shown);
                out.push_str(shown);
            }
            "para" | "br" | "/para" => out.push_str("\n\n"),
            _ => {}
        }
        rest = &rest[lt + gt + 1..];
    }
    out.push_str(rest);
    let text = decode_entities(&out);
    // Folded per paragraph: the comment's own line breaks are layout, the
    // blank lines between paragraphs are meaning.
    text.split("\n\n")
        .map(|paragraph| paragraph.split_whitespace().collect::<Vec<_>>().join(" "))
        .filter(|paragraph| !paragraph.is_empty())
        .collect::<Vec<_>>()
        .join("\n\n")
}

fn decode_entities(text: &str) -> String {
    text.replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&quot;", "\"")
        .replace("&apos;", "'")
        .replace("&amp;", "&")
}

/// The type or namespace a member is in, as the hover names it:
/// `System.Linq.IGrouping<int, Item>` with the type arguments it has at
/// the use, and with its own type parameters where they stand for nothing
/// known — never as metadata spells it, `IGrouping`2`.
fn container_name(
    compilation: &rustlyn_semantics::Compilation,
    container: SymbolId,
    arguments: &HashMap<SymbolId, Type>,
) -> String {
    let symbols = compilation.symbols();
    let found = symbols.get(container);
    let name = symbols.qualified_name(container);
    let Some(detail) = found
        .as_named_type()
        .filter(|detail| !detail.type_parameters.is_empty())
    else {
        return name;
    };
    if compilation.anonymous_names(container).is_some() {
        let ty = Type::Named {
            symbol: container,
            type_arguments: detail
                .type_parameters
                .iter()
                .map(|&parameter| Type::TypeParameter(parameter).substitute(arguments))
                .collect(),
        };
        return super::display_type(compilation, &ty);
    }
    let shown: Vec<String> = detail
        .type_parameters
        .iter()
        .map(|&parameter| {
            super::display_type(
                compilation,
                &Type::TypeParameter(parameter).substitute(arguments),
            )
        })
        .collect();
    format!(
        "{}<{}>",
        name.split('`').next().unwrap_or_default(),
        shown.join(", ")
    )
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::super::tests::{at, compile};
    use super::*;

    fn messages(semantic: &Semantic, text: Option<&str>) -> Vec<String> {
        semantic
            .diagnostics(Path::new("/p/C.cs"), text)
            .expect("in the compilation")
            .iter()
            .map(|diagnostic| format!("{}@{}", diagnostic.code(), diagnostic.span().start()))
            .collect()
    }

    #[test]
    fn a_file_reports_its_syntax_and_its_bodies() {
        let text = "class C {\n  void M() { int x = y; }\n}\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let found = messages(&semantic, None);
        assert_eq!(
            found,
            vec![format!("CS0103@{}", at(text, "y;", 0))],
            "{found:?}"
        );

        // The editor's text, unsaved: the error moved with the edit, and a
        // missing semicolon is reported where it is now.
        let edited = "class C {\n  // moved\n  void M() { int x = y; int z = 1 }\n}\n";
        let found = messages(&semantic, Some(edited));
        assert!(
            found.contains(&format!("CS0103@{}", at(edited, "y;", 0))),
            "{found:?}"
        );
        assert!(found.iter().any(|m| m.starts_with("CS1002")), "{found:?}");
    }

    #[test]
    fn a_clean_file_has_nothing_to_report() {
        let text = "class C {\n  int f = 1;\n  void M() { var x = f + 1; }\n}\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        assert!(messages(&semantic, None).is_empty());
    }

    #[test]
    fn a_call_being_typed_shows_its_overloads_and_the_parameter() {
        let text = "class C {\n  void Log(string message) { }\n  void Log(string format, int count) { }\n  void M() { Log(\"a\", 2); }\n}\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let found = semantic
            .signatures(Path::new("/p/C.cs"), at(text, "2);", 0), None)
            .expect("in an argument list");
        assert_eq!(found.items.len(), 2);
        assert_eq!(found.parameter, 1);
        let active = &found.items[found.active];
        assert_eq!(active.label, "void Log(string format, int count)");
        let (a, b) = active.parameters[1];
        assert_eq!(&active.label[a as usize..b as usize], "int count");

        // Still being typed: `Log(` with nothing after it, which binds to
        // no overload yet.
        let typing = "class C {\n  void Log(string message) { }\n  void Log(string format, int count) { }\n  void M() { Log( }\n}\n";
        let found = semantic
            .signatures(Path::new("/p/C.cs"), at(typing, "Log( ", 4), Some(typing))
            .expect("an unfinished call");
        assert_eq!(found.items.len(), 2);
        assert_eq!(found.parameter, 0);

        // Outside the parentheses there is nothing to show.
        assert!(
            semantic
                .signatures(Path::new("/p/C.cs"), at(text, "Log(\"a", 0), None)
                .is_none()
        );
    }

    #[test]
    fn a_call_typed_into_an_unsaved_body_shows_its_signature() {
        let pawn = "namespace Game;\npublic class Pawn { public int Health; public void Hit(int a, int b) { } }\n";
        let text = "namespace Game;\npublic class Use { void M(Pawn p) { var n = p.Health; } }\n";
        let semantic = compile(&[("Pawn.cs", pawn), ("C.cs", text)], false).expect("compiled");
        let typed = "namespace Game;\npublic class Use { void M(Pawn p) { var n = p.Health; p.Hit(1, ); } }\n";
        let found = semantic
            .signatures(Path::new("/p/C.cs"), at(typed, ", )", 2), Some(typed))
            .expect("the call being typed");
        assert_eq!(found.items[found.active].label, "void Hit(int a, int b)");
        assert_eq!(found.parameter, 1);
    }

    #[test]
    fn a_constructor_call_shows_the_constructors() {
        let text = "class P { public P(int x) { } public P(int x, int y) { } }\nclass C { void M() { var p = new P(1, 2); } }\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let found = semantic
            .signatures(Path::new("/p/C.cs"), at(text, "2);", 0), None)
            .expect("constructors");
        assert_eq!(found.items.len(), 2);
        assert_eq!(found.items[found.active].label, "P(int x, int y)");
        assert_eq!(found.parameter, 1);
    }

    #[test]
    fn documentation_comes_from_the_comment_above() {
        let text = "class C {\n  /// <summary>Adds <paramref name=\"n\"/> points to <see cref=\"T:Game.Score\"/>.</summary>\n  /// <param name=\"n\">How many.</param>\n  /// <returns>The new total.</returns>\n  public int Add(int n) => n;\n  void M() { Add(1); }\n}\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let found = semantic
            .documentation(Path::new("/p/C.cs"), at(text, "Add(1)", 0), None)
            .expect("documented");
        assert_eq!(found.signature, "int Add(int n)");
        assert_eq!(found.container, "C");
        assert_eq!(found.summary, "Adds n points to Score.");
        assert_eq!(
            found.parameters,
            vec![("n".to_string(), "How many.".to_string())]
        );
        assert_eq!(found.returns, "The new total.");
    }

    /// The signature is the symbol as this use has it: the receiver's type
    /// arguments, the ones a call inferred, the type `var` stands for.
    #[test]
    fn documentation_shows_the_symbol_as_constructed_here() {
        let text = "class Group<TKey, TItem> { public TKey Key; }\n\
                    class Item { }\n\
                    static class Seq { public static TOut Map<TIn, TOut>(this Group<int, TIn> group, System.Func<TIn, TOut> f) => default; }\n\
                    class C { void M(Group<int, Item> g) { var k = g.Key; var s = g.Map(item => \"x\"); var anon = new { Name = \"a\", Size = 1 }; var copy = g; } }\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let documentation = |marker: &str, into: usize| {
            semantic
                .documentation(Path::new("/p/C.cs"), at(text, marker, into), None)
                .expect("documented")
        };
        let key = documentation("g.Key", 2);
        assert_eq!(key.signature, "int Key");
        assert_eq!(key.container, "Group<int, Item>");
        assert_eq!(
            documentation("g.Map", 2).signature,
            "string Map<Item, string>(this Group<int, Item> group, Func<Item, string> f)"
        );
        assert_eq!(documentation("item =>", 0).signature, "Item item");
        assert_eq!(
            documentation("var copy", 0).signature,
            "class Group<int, Item>"
        );
        assert_eq!(
            documentation("anon", 0).signature,
            "new { string Name, int Size } anon"
        );
    }

    #[test]
    fn xml_documentation_is_read_by_member_id() {
        let docs = parse_xml_members(
            "<doc><members>\n<member name=\"T:N.Box`1\"><summary>A box.</summary></member>\n<member name=\"M:N.Box`1.Put(`0,System.Int32)\"><summary>Puts.</summary></member>\n<member name=\"M:N.Box`1.Put(`0)\"><summary>Puts one.</summary></member>\n</members></doc>",
        );
        assert!(
            docs.get("T:N.Box`1")
                .is_some_and(|xml| xml.contains("A box."))
        );
        assert!(
            docs.method("M:N.Box`1.Put", 2)
                .is_some_and(|xml| xml.contains("Puts."))
        );
        assert!(
            docs.method("M:N.Box`1.Put", 1)
                .is_some_and(|xml| xml.contains("Puts one."))
        );
        assert_eq!(
            parse_documentation("<summary>\n  Line one\n  goes on.<para>Two.</para></summary>")
                .summary,
            "Line one goes on.\n\nTwo."
        );
    }

    #[test]
    fn an_attribute_is_used_by_its_short_name() {
        let text = "class MarkAttribute : System.Attribute { }\n[Mark] class C { }\n";
        let semantic =
            compile(&[("C.cs", text)], true).or_else(|| compile(&[("C.cs", text)], false));
        let Some(semantic) = semantic else { return };
        let (_, found) = semantic
            .references(Path::new("/p/C.cs"), at(text, "MarkAttribute", 0), None)
            .expect("resolved");
        let starts: Vec<u32> = found.iter().map(|(_, span)| span.start()).collect();
        assert!(starts.contains(&at(text, "Mark]", 0)), "{starts:?}");
    }

    #[test]
    fn a_file_reports_what_its_declarations_get_wrong() {
        // A type a signature names that does not exist, and an interface
        // member the class never wrote: neither is in any body.
        let text = "interface IShape { int Area(); }\nclass C : IShape {\n  Nonesuch f;\n}\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let found = messages(&semantic, None);
        assert_eq!(
            found,
            vec![
                format!("CS0535@{}", at(text, "IShape {\n", 0)),
                format!("CS0246@{}", at(text, "Nonesuch", 0)),
            ],
            "{found:?}"
        );

        // Typed above them, unsaved: both move with the text.
        let edited = format!("// a comment\n{text}");
        let found = messages(&semantic, Some(&edited));
        assert!(
            found.contains(&format!("CS0246@{}", at(&edited, "Nonesuch", 0))),
            "{found:?}"
        );
    }
}
