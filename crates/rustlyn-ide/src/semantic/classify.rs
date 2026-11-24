//! Semantic classification: what colour a name is, once it is known what it
//! names.
//!
//! Layer 2 colours by spelling, and a name's spelling says nothing about it:
//! `Health` may be a field, a property or a type, and `record` may be a
//! keyword or a local called `record`. This answers with what the compiler
//! decided, in the classes Roslyn's semantic classifier uses — class name,
//! struct name, method name, extension method name, local name, and the rest
//! — plus modifiers in the manner of LSP semantic tokens: static, reassigned,
//! deprecated, abstract, readonly, async, declaration, and from a referenced
//! library.
//!
//! It is asked for a window, and costs what the window costs. Only the tokens
//! in the range are looked at, and only the bodies those tokens are in are
//! bound — the view keeps each body for the next token in it, and the
//! compilation keeps it for the next repaint. The one thing that looks past
//! the window is "reassigned", which is a fact about a whole body: a local
//! written below the screen is reassigned on it too. That scan is of bodies
//! already bound, once per body.

use std::collections::{HashMap, HashSet};
use std::path::Path;

use rustlyn_semantics::{MethodKind, Modifiers, SemanticModel, SymbolId, SymbolKind, TypeKind};
use rustlyn_syntax::{SyntaxElement, SyntaxKind, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::references::is_written;
use super::{Resolved, Semantic, View, names_declaration};

/// What a name is, as Roslyn's `ClassificationTypeNames` has it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum SemanticClass {
    ClassName = 0,
    RecordClassName,
    StructName,
    RecordStructName,
    InterfaceName,
    EnumName,
    DelegateName,
    TypeParameterName,
    NamespaceName,
    MethodName,
    ExtensionMethodName,
    PropertyName,
    EventName,
    FieldName,
    ConstantName,
    EnumMemberName,
    LocalName,
    ParameterName,
    LabelName,
    /// A contextual keyword acting as one: `var` for an inferred type,
    /// `nameof`, `dynamic`, `global::`, `notnull`, `async`, `await`, `yield`.
    Keyword,
}

impl SemanticClass {
    /// How many classes there are, for a caller's table.
    #[must_use]
    pub const fn count() -> u32 {
        Self::Keyword as u32 + 1
    }

    /// The name Roslyn gives the class: what a theme written for Visual
    /// Studio keys its colours by.
    #[must_use]
    pub const fn roslyn_name(self) -> &'static str {
        match self {
            Self::ClassName => "class name",
            Self::RecordClassName => "record class name",
            Self::StructName => "struct name",
            Self::RecordStructName => "record struct name",
            Self::InterfaceName => "interface name",
            Self::EnumName => "enum name",
            Self::DelegateName => "delegate name",
            Self::TypeParameterName => "type parameter name",
            Self::NamespaceName => "namespace name",
            Self::MethodName => "method name",
            Self::ExtensionMethodName => "extension method name",
            Self::PropertyName => "property name",
            Self::EventName => "event name",
            Self::FieldName => "field name",
            Self::ConstantName => "constant name",
            Self::EnumMemberName => "enum member name",
            Self::LocalName => "local name",
            Self::ParameterName => "parameter name",
            Self::LabelName => "label name",
            Self::Keyword => "keyword",
        }
    }
}

/// What else is true of a classified name, as a bit set.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct SemanticModifiers(u32);

impl SemanticModifiers {
    /// Roslyn's additive "static symbol": a static member or type, or a
    /// constant.
    pub const STATIC: Self = Self(1 << 0);
    /// Roslyn's "reassigned variable": a local or parameter written
    /// somewhere after its declaration.
    pub const REASSIGNED: Self = Self(1 << 1);
    /// Declared with `[Obsolete]`.
    pub const DEPRECATED: Self = Self(1 << 2);
    pub const ABSTRACT: Self = Self(1 << 3);
    /// `readonly` or `const`.
    pub const READONLY: Self = Self(1 << 4);
    pub const ASYNC: Self = Self(1 << 5);
    /// This name is the one its declaration gives.
    pub const DECLARATION: Self = Self(1 << 6);
    /// Declared in a referenced assembly, not in the project.
    pub const DEFAULT_LIBRARY: Self = Self(1 << 7);

    #[must_use]
    pub const fn empty() -> Self {
        Self(0)
    }

    #[must_use]
    pub const fn bits(self) -> u32 {
        self.0
    }

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    pub const fn insert(&mut self, other: Self) {
        self.0 |= other.0;
    }

    const fn with(mut self, other: Self, when: bool) -> Self {
        if when {
            self.0 |= other.0;
        }
        self
    }
}

impl std::fmt::Debug for SemanticModifiers {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let names = [
            (Self::STATIC, "static"),
            (Self::REASSIGNED, "reassigned"),
            (Self::DEPRECATED, "deprecated"),
            (Self::ABSTRACT, "abstract"),
            (Self::READONLY, "readonly"),
            (Self::ASYNC, "async"),
            (Self::DECLARATION, "declaration"),
            (Self::DEFAULT_LIBRARY, "library"),
        ];
        let present: Vec<&str> = names
            .iter()
            .filter(|(flag, _)| self.contains(*flag))
            .map(|(_, name)| *name)
            .collect();
        write!(f, "[{}]", present.join(" "))
    }
}

/// One classified name, in bytes of the text asked about.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemanticToken {
    pub span: TextSpan,
    pub class: SemanticClass,
    pub modifiers: SemanticModifiers,
}

impl Semantic {
    /// Every name in `range` of `path`, classified by what it refers to, in
    /// order. Names nothing binds are left out, for the syntactic colour to
    /// stand; so is punctuation and every keyword that is always one.
    #[must_use]
    pub fn semantic_tokens(
        &self,
        path: &Path,
        range: TextSpan,
        text: Option<&str>,
    ) -> Option<Vec<SemanticToken>> {
        let mut view = self.view_of(path, text)?;
        let mut tokens = Vec::new();
        tokens_in(&view.root.clone(), range, &mut tokens);
        let mut classifier = Classifier {
            view: &mut view,
            written: HashMap::new(),
            obsolete: HashMap::new(),
        };
        Some(
            tokens
                .iter()
                .filter_map(|token| {
                    let (class, modifiers) = classifier.classify(token)?;
                    Some(SemanticToken {
                        span: token.span(),
                        class,
                        modifiers,
                    })
                })
                .collect(),
        )
    }
}

/// The tokens of `node` that overlap `range`, not descending into anything
/// that does not.
fn tokens_in(node: &SyntaxNode, range: TextSpan, out: &mut Vec<SyntaxToken>) {
    for child in node.children_with_tokens() {
        let full = child.full_span();
        if full.end() <= range.start() || full.start() >= range.end() {
            continue;
        }
        match child {
            SyntaxElement::Token(token) => {
                let span = token.span();
                if span.start() < range.end() && span.end() > range.start() {
                    out.push(token);
                }
            }
            SyntaxElement::Node(child) => tokens_in(&child, range, out),
        }
    }
}

/// A variable that can be reassigned: a local by where it was declared, a
/// parameter by its symbol.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Variable {
    Local(TextSpan),
    Parameter(SymbolId),
}

struct Classifier<'v, 'a> {
    view: &'v mut View<'a>,
    /// The variables written in each body, by the body's span.
    written: HashMap<TextSpan, HashSet<Variable>>,
    obsolete: HashMap<SymbolId, bool>,
}

impl Classifier<'_, '_> {
    fn classify(&mut self, token: &SyntaxToken) -> Option<(SemanticClass, SemanticModifiers)> {
        let none = SemanticModifiers::empty();
        let kind = token.kind();
        if kind != SyntaxKind::IdentifierToken {
            // A contextual keyword the parser took as one.
            return (kind.is_contextual_keyword() && kind != SyntaxKind::UnderscoreToken)
                .then_some((SemanticClass::Keyword, none));
        }
        let parent = token.parent().clone();
        let grand = parent.parent().cloned();
        let text = token.value_text();

        match parent.kind() {
            SyntaxKind::LabeledStatement => {
                return Some((SemanticClass::LabelName, SemanticModifiers::DECLARATION));
            }
            SyntaxKind::GotoStatement => return Some((SemanticClass::LabelName, none)),
            _ => {}
        }
        let is_first_of = |kinds: &[SyntaxKind]| {
            parent.kind() == SyntaxKind::IdentifierName
                && grand.as_ref().is_some_and(|grand| {
                    kinds.contains(&grand.kind())
                        && grand.children().next().as_ref() == Some(&parent)
                })
        };
        // `global::System`.
        if text == "global" && is_first_of(&[SyntaxKind::AliasQualifiedName]) {
            return Some((SemanticClass::Keyword, none));
        }
        // `var x = ...`, unless someone declared a type called `var`.
        if text == "var"
            && is_first_of(&[
                SyntaxKind::VariableDeclaration,
                SyntaxKind::ForEachStatement,
                SyntaxKind::ForEachVariableStatement,
                SyntaxKind::DeclarationExpression,
                SyntaxKind::DeclarationPattern,
            ])
        {
            let binder = self.view.model.binder();
            let context = binder.context_at(self.view.tree, &parent);
            if binder.lookup("var", 0, &context).is_none() {
                return Some((SemanticClass::Keyword, none));
            }
        }

        let resolved = self.view.resolve_use(token);
        let names_type_called = |resolved: &Option<Resolved>, name: &str| match resolved {
            Some(Resolved::Symbol(symbol)) => {
                let found = self.view.compilation().symbols().get(*symbol);
                found.kind == SymbolKind::NamedType && found.name == name
            }
            _ => false,
        };
        match text {
            "nameof"
                if is_first_of(&[SyntaxKind::InvocationExpression])
                    && !matches!(&resolved, Some(Resolved::Symbol(symbol))
                        if self.view.compilation().symbols().get(*symbol).kind == SymbolKind::Method) =>
            {
                return Some((SemanticClass::Keyword, none));
            }
            "dynamic"
                if parent.kind() == SyntaxKind::IdentifierName
                    && !matches!(resolved, Some(Resolved::Local { .. }))
                    && !names_type_called(&resolved, "dynamic")
                    && !matches!(&resolved, Some(Resolved::Symbol(symbol))
                        if self.view.compilation().symbols().get(*symbol).kind != SymbolKind::NamedType) =>
            {
                return Some((SemanticClass::Keyword, none));
            }
            "notnull" | "unmanaged"
                if grand
                    .as_ref()
                    .is_some_and(|grand| grand.kind() == SyntaxKind::TypeConstraint)
                    && !names_type_called(&resolved, text) =>
            {
                return Some((SemanticClass::Keyword, none));
            }
            _ => {}
        }

        match resolved? {
            Resolved::Local { span, .. } => Some(self.local(token, span)),
            Resolved::Symbol(symbol) => self.symbol(token, &parent, symbol),
        }
    }

    /// A local, or a lambda's parameter: the binder keeps both on the body's
    /// table, and only the declaration says which.
    fn local(
        &mut self,
        token: &SyntaxToken,
        declared: TextSpan,
    ) -> (SemanticClass, SemanticModifiers) {
        let declaration = self
            .view
            .root
            .find_token(declared.start())
            .map(|token| token.parent().clone());
        let is_parameter = declaration
            .as_ref()
            .is_some_and(|node| node.kind() == SyntaxKind::Parameter);
        let is_constant = declaration.as_ref().is_some_and(|node| {
            node.ancestors()
                .find(|ancestor| ancestor.kind() == SyntaxKind::LocalDeclarationStatement)
                .is_some_and(|statement| {
                    statement
                        .child_token_of_kind(SyntaxKind::ConstKeyword)
                        .is_some()
                })
        });
        let class = if is_parameter {
            SemanticClass::ParameterName
        } else if is_constant {
            SemanticClass::ConstantName
        } else {
            SemanticClass::LocalName
        };
        let modifiers = SemanticModifiers::empty()
            .with(SemanticModifiers::DECLARATION, declared == token.span())
            .with(SemanticModifiers::READONLY, is_constant)
            .with(
                SemanticModifiers::REASSIGNED,
                !is_constant && self.is_reassigned(token, Variable::Local(declared)),
            );
        (class, modifiers)
    }

    fn symbol(
        &mut self,
        token: &SyntaxToken,
        parent: &SyntaxNode,
        symbol: SymbolId,
    ) -> Option<(SemanticClass, SemanticModifiers)> {
        let compilation = self.view.compilation();
        let symbols = compilation.symbols();
        let found = symbols.get(symbol);
        let declares = names_declaration(parent, token);
        // A constructor is named by its type, and coloured as it.
        let is_constructor = found.as_method().is_some_and(|method| {
            matches!(
                method.method_kind,
                MethodKind::Constructor | MethodKind::StaticConstructor | MethodKind::Destructor
            )
        });
        let described = if is_constructor {
            found.container?
        } else {
            symbol
        };
        let described_symbol = symbols.get(described);
        let in_enum = |symbol: SymbolId| {
            symbols
                .get(symbol)
                .container
                .is_some_and(|container| symbols.get(container).type_kind() == Some(TypeKind::Enum))
        };
        let is_extension = described_symbol
            .as_method()
            .is_some_and(|method| method.is_extension);
        let class = match described_symbol.kind {
            SymbolKind::Namespace => SemanticClass::NamespaceName,
            SymbolKind::NamedType => match described_symbol.type_kind() {
                Some(TypeKind::Record) => SemanticClass::RecordClassName,
                Some(TypeKind::Struct) => SemanticClass::StructName,
                Some(TypeKind::RecordStruct) => SemanticClass::RecordStructName,
                Some(TypeKind::Interface) => SemanticClass::InterfaceName,
                Some(TypeKind::Enum) => SemanticClass::EnumName,
                Some(TypeKind::Delegate) => SemanticClass::DelegateName,
                Some(TypeKind::Class) | None => SemanticClass::ClassName,
            },
            SymbolKind::Method if is_extension => SemanticClass::ExtensionMethodName,
            SymbolKind::Method => SemanticClass::MethodName,
            SymbolKind::Field if in_enum(described) => SemanticClass::EnumMemberName,
            SymbolKind::Field if described_symbol.modifiers.contains(Modifiers::CONST) => {
                SemanticClass::ConstantName
            }
            SymbolKind::Field => SemanticClass::FieldName,
            SymbolKind::Property => SemanticClass::PropertyName,
            SymbolKind::Event => SemanticClass::EventName,
            SymbolKind::Parameter => SemanticClass::ParameterName,
            SymbolKind::TypeParameter => SemanticClass::TypeParameterName,
            SymbolKind::Local => SemanticClass::LocalName,
        };
        let flags = described_symbol.modifiers;
        let is_constant = described_symbol.kind == SymbolKind::Field
            && (flags.contains(Modifiers::CONST) || in_enum(described));
        // An extension method called on its receiver is called as an
        // instance method, which is how Roslyn colours it.
        let is_static = !matches!(described_symbol.kind, SymbolKind::Namespace)
            && (flags.contains(Modifiers::STATIC) || (is_constant && !in_enum(described)))
            && (!is_extension || declares);
        let from_metadata = compilation.is_from_metadata(described);
        let mut modifiers = SemanticModifiers::empty()
            .with(SemanticModifiers::STATIC, is_static)
            .with(
                SemanticModifiers::ABSTRACT,
                flags.contains(Modifiers::ABSTRACT),
            )
            .with(
                SemanticModifiers::READONLY,
                flags.contains(Modifiers::READONLY) || is_constant,
            )
            .with(SemanticModifiers::ASYNC, flags.contains(Modifiers::ASYNC))
            .with(SemanticModifiers::DECLARATION, declares)
            .with(SemanticModifiers::DEFAULT_LIBRARY, from_metadata);
        if !from_metadata && self.is_obsolete(described) {
            modifiers.insert(SemanticModifiers::DEPRECATED);
        }
        if described_symbol.kind == SymbolKind::Parameter
            && self.is_reassigned(token, Variable::Parameter(described))
        {
            modifiers.insert(SemanticModifiers::REASSIGNED);
        }
        Some((class, modifiers))
    }

    /// Whether `variable`, named by `token`, is written anywhere in the body
    /// the token is in other than where it is declared.
    fn is_reassigned(&mut self, token: &SyntaxToken, variable: Variable) -> bool {
        let Some(owner) = SemanticModel::body_owner(token.parent()) else {
            return false;
        };
        if !self.written.contains_key(&owner.span()) {
            let targets: Vec<SyntaxToken> = owner
                .descendant_tokens()
                .filter(|token| token.kind() == SyntaxKind::IdentifierToken && is_written(token))
                .collect();
            let mut written = HashSet::new();
            for target in targets {
                match self.view.resolve_use(&target) {
                    Some(Resolved::Local { span, .. }) => {
                        written.insert(Variable::Local(span));
                    }
                    Some(Resolved::Symbol(symbol))
                        if self.view.compilation().symbols().get(symbol).kind
                            == SymbolKind::Parameter =>
                    {
                        written.insert(Variable::Parameter(symbol));
                    }
                    _ => {}
                }
            }
            self.written.insert(owner.span(), written);
        }
        self.written[&owner.span()].contains(&variable)
    }

    /// Whether a declaration of `symbol` carries `[Obsolete]`.
    fn is_obsolete(&mut self, symbol: SymbolId) -> bool {
        if let Some(&known) = self.obsolete.get(&symbol) {
            return known;
        }
        let compilation = self.view.compilation();
        let obsolete = compilation
            .symbols()
            .get(symbol)
            .locations
            .iter()
            .any(|location| {
                let Some(tree) = compilation.trees().get(location.tree) else {
                    return false;
                };
                let Some(token) = tree.root().find_token(location.span.start()) else {
                    return false;
                };
                let declaration = std::iter::once(token.parent().clone())
                    .chain(token.parent().ancestors())
                    .find(|node| is_attributable(node.kind()));
                declaration.is_some_and(|declaration| has_obsolete_attribute(&declaration))
            });
        self.obsolete.insert(symbol, obsolete);
        obsolete
    }
}

/// Whether a node is a declaration attributes can be written on.
const fn is_attributable(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::ClassDeclaration
            | SyntaxKind::StructDeclaration
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::RecordDeclaration
            | SyntaxKind::RecordStructDeclaration
            | SyntaxKind::EnumDeclaration
            | SyntaxKind::DelegateDeclaration
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::ConstructorDeclaration
            | SyntaxKind::DestructorDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::IndexerDeclaration
            | SyntaxKind::EventDeclaration
            | SyntaxKind::EventFieldDeclaration
            | SyntaxKind::FieldDeclaration
            | SyntaxKind::EnumMemberDeclaration
            | SyntaxKind::OperatorDeclaration
            | SyntaxKind::ConversionOperatorDeclaration
            | SyntaxKind::LocalFunctionStatement
            | SyntaxKind::Parameter
    )
}

fn has_obsolete_attribute(declaration: &SyntaxNode) -> bool {
    declaration
        .children()
        .filter(|child| child.kind() == SyntaxKind::AttributeList)
        .flat_map(|list| list.children())
        .filter(|child| child.kind() == SyntaxKind::Attribute)
        .any(|attribute| {
            attribute.children().next().is_some_and(|name| {
                let written = name.text();
                let last = written.trim().rsplit(['.', ':']).next().unwrap_or("");
                matches!(last.trim(), "Obsolete" | "ObsoleteAttribute")
            })
        })
}

#[cfg(test)]
mod tests {
    use super::super::tests::compile;
    use super::*;

    /// Every classified name of `text`, as `(text, class, modifiers)`.
    fn classified(
        semantic: &Semantic,
        text: &str,
    ) -> Vec<(String, SemanticClass, SemanticModifiers)> {
        semantic
            .semantic_tokens(
                Path::new("/p/C.cs"),
                TextSpan::new(0, text.len() as u32),
                Some(text),
            )
            .expect("classified")
            .into_iter()
            .map(|token| {
                (
                    text[token.span.start() as usize..token.span.end() as usize].to_string(),
                    token.class,
                    token.modifiers,
                )
            })
            .collect()
    }

    /// The class and modifiers of the `nth` (from zero) classified name
    /// spelled `word`.
    fn class_of(
        found: &[(String, SemanticClass, SemanticModifiers)],
        word: &str,
        nth: usize,
    ) -> (SemanticClass, SemanticModifiers) {
        found
            .iter()
            .filter(|(text, _, _)| text == word)
            .nth(nth)
            .map(|(_, class, modifiers)| (*class, *modifiers))
            .unwrap_or_else(|| panic!("no {word} #{nth} in {found:?}"))
    }

    fn file(text: &str) -> (Semantic, Vec<(String, SemanticClass, SemanticModifiers)>) {
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let found = classified(&semantic, text);
        (semantic, found)
    }

    #[test]
    fn types_are_coloured_by_what_they_are() {
        let text = "namespace Game.Core {\n\
                    interface IShape { }\n\
                    struct Point { }\n\
                    record Person(string Name);\n\
                    record struct Pair(int A, int B);\n\
                    enum Color { Red, Green }\n\
                    delegate void Handler(int code);\n\
                    abstract class Shape<T> : IShape { Point p; Color c = Color.Red; Handler h; Person who; Pair pair; T value; }\n\
                    static class Tools { }\n\
                    }\n";
        let (_, found) = file(text);
        use SemanticClass as C;
        assert_eq!(class_of(&found, "Game", 0).0, C::NamespaceName);
        assert_eq!(class_of(&found, "Core", 0).0, C::NamespaceName);
        assert_eq!(class_of(&found, "IShape", 1).0, C::InterfaceName);
        assert_eq!(class_of(&found, "Point", 1).0, C::StructName);
        assert_eq!(class_of(&found, "Person", 1).0, C::RecordClassName);
        assert_eq!(class_of(&found, "Pair", 1).0, C::RecordStructName);
        assert_eq!(class_of(&found, "Color", 1).0, C::EnumName);
        assert_eq!(class_of(&found, "Red", 1).0, C::EnumMemberName);
        assert_eq!(class_of(&found, "Handler", 1).0, C::DelegateName);
        assert_eq!(class_of(&found, "T", 1).0, C::TypeParameterName);
        let (class, modifiers) = class_of(&found, "Shape", 0);
        assert_eq!(class, C::ClassName);
        assert!(modifiers.contains(SemanticModifiers::ABSTRACT));
        assert!(modifiers.contains(SemanticModifiers::DECLARATION));
        let (class, modifiers) = class_of(&found, "Tools", 0);
        assert_eq!(class, C::ClassName);
        assert!(modifiers.contains(SemanticModifiers::STATIC));
        // A record's positional parameter is a parameter where it is written.
        assert_eq!(class_of(&found, "Name", 0).0, C::ParameterName);
    }

    #[test]
    fn members_are_coloured_by_what_they_are() {
        let text = "using System;\n\
                    static class Extensions { public static int Twice(this int x) => x * 2; }\n\
                    class Player {\n\
                      public const int Max = 100;\n\
                      public static int Count;\n\
                      readonly int health;\n\
                      public int Health { get { return health; } }\n\
                      public event Action Died;\n\
                      public async void Hit(int damage) { Count++; Died?.Invoke(); var twice = damage.Twice(); var m = Max; }\n\
                    }\n";
        let (_, found) = file(text);
        use SemanticClass as C;
        use SemanticModifiers as M;
        let (class, modifiers) = class_of(&found, "Max", 1);
        assert_eq!(class, C::ConstantName);
        assert!(modifiers.contains(M::STATIC) && modifiers.contains(M::READONLY));
        let (class, modifiers) = class_of(&found, "Count", 1);
        assert_eq!(class, C::FieldName);
        assert!(modifiers.contains(M::STATIC));
        let (class, modifiers) = class_of(&found, "health", 1);
        assert_eq!(class, C::FieldName);
        assert!(modifiers.contains(M::READONLY));
        assert!(!modifiers.contains(M::STATIC));
        assert_eq!(class_of(&found, "Health", 0).0, C::PropertyName);
        assert_eq!(class_of(&found, "Died", 1).0, C::EventName);
        let (class, modifiers) = class_of(&found, "Hit", 0);
        assert_eq!(class, C::MethodName);
        assert!(modifiers.contains(M::ASYNC) && modifiers.contains(M::DECLARATION));
        // Declared static, called as an instance method.
        let (class, modifiers) = class_of(&found, "Twice", 0);
        assert_eq!(class, C::ExtensionMethodName);
        assert!(modifiers.contains(M::STATIC));
        let (class, modifiers) = class_of(&found, "Twice", 1);
        assert_eq!(class, C::ExtensionMethodName);
        assert!(!modifiers.contains(M::STATIC));
        assert_eq!(class_of(&found, "Invoke", 0).0, C::MethodName);
        assert_eq!(class_of(&found, "damage", 1).0, C::ParameterName);
    }

    #[test]
    fn locals_parameters_and_what_is_written_to_them() {
        let text = "using System;\n\
                    class C {\n\
                      int Sum(int[] items, int start, ref int calls) {\n\
                        const int Limit = 10;\n\
                        var total = start;\n\
                        int fixedOne = 1;\n\
                        foreach (var item in items) { total += item; }\n\
                        calls++;\n\
                        Func<int, int> twice = n => n * 2;\n\
                        again: if (total > Limit) goto again;\n\
                        return twice(total) + fixedOne;\n\
                      }\n\
                    }\n";
        let (_, found) = file(text);
        use SemanticClass as C;
        use SemanticModifiers as M;
        let (class, modifiers) = class_of(&found, "total", 0);
        assert_eq!(class, C::LocalName);
        assert!(modifiers.contains(M::DECLARATION) && modifiers.contains(M::REASSIGNED));
        let (_, modifiers) = class_of(&found, "total", 2);
        assert!(modifiers.contains(M::REASSIGNED) && !modifiers.contains(M::DECLARATION));
        let (class, modifiers) = class_of(&found, "fixedOne", 1);
        assert_eq!(class, C::LocalName);
        assert!(!modifiers.contains(M::REASSIGNED));
        let (class, modifiers) = class_of(&found, "calls", 0);
        assert_eq!(class, C::ParameterName);
        assert!(modifiers.contains(M::REASSIGNED));
        let (_, modifiers) = class_of(&found, "start", 1);
        assert!(!modifiers.contains(M::REASSIGNED));
        let (class, modifiers) = class_of(&found, "Limit", 1);
        assert_eq!(class, C::ConstantName);
        assert!(modifiers.contains(M::READONLY));
        assert_eq!(class_of(&found, "n", 0).0, C::ParameterName);
        assert_eq!(class_of(&found, "n", 1).0, C::ParameterName);
        assert_eq!(class_of(&found, "item", 0).0, C::LocalName);
        assert_eq!(class_of(&found, "twice", 1).0, C::LocalName);
        assert_eq!(class_of(&found, "again", 0).0, C::LabelName);
        assert_eq!(class_of(&found, "again", 1).0, C::LabelName);
        assert_eq!(class_of(&found, "var", 0).0, C::Keyword);
        assert_eq!(class_of(&found, "Func", 0).0, C::DelegateName);
    }

    #[test]
    fn contextual_keywords_are_keywords_only_where_they_act_as_one() {
        let text = "using G = global::System;\n\
                    class C<T> where T : notnull {\n\
                      int value;\n\
                      int P { get => value; set { this.value = value; } }\n\
                      async System.Threading.Tasks.Task M() { var record = 1; var n = nameof(record); await M(); }\n\
                      dynamic D() => null;\n\
                    }\n\
                    record R(int A);\n";
        let (_, found) = file(text);
        use SemanticClass as C;
        assert_eq!(class_of(&found, "global", 0).0, C::Keyword);
        assert_eq!(class_of(&found, "notnull", 0).0, C::Keyword);
        assert_eq!(class_of(&found, "async", 0).0, C::Keyword);
        assert_eq!(class_of(&found, "await", 0).0, C::Keyword);
        assert_eq!(class_of(&found, "nameof", 0).0, C::Keyword);
        assert_eq!(class_of(&found, "dynamic", 0).0, C::Keyword);
        assert_eq!(class_of(&found, "record", 0).0, C::LocalName);
        assert_eq!(class_of(&found, "record", 1).0, C::LocalName);
        assert_eq!(class_of(&found, "record", 2).0, C::Keyword);
        // The field, then the accessor's implicit parameter.
        assert_eq!(class_of(&found, "value", 2).0, C::FieldName);
        assert_eq!(class_of(&found, "value", 3).0, C::ParameterName);
    }

    #[test]
    fn attributes_constructors_and_obsolete_members() {
        let text = "using System;\n\
                    class TagAttribute : Attribute { }\n\
                    [Tag] class Old { [Obsolete] public static void Gone() { } public Old() { } }\n\
                    class Use { void M() { Old.Gone(); var o = new Old(); } }\n";
        let (_, found) = file(text);
        use SemanticClass as C;
        assert_eq!(class_of(&found, "Tag", 0).0, C::ClassName);
        let (class, modifiers) = class_of(&found, "Gone", 1);
        assert_eq!(class, C::MethodName);
        assert!(
            modifiers.contains(SemanticModifiers::DEPRECATED),
            "{modifiers:?}"
        );
        assert!(modifiers.contains(SemanticModifiers::STATIC));
        // `public Old()` and `new Old()` are the class.
        assert_eq!(class_of(&found, "Old", 1).0, C::ClassName);
        assert_eq!(class_of(&found, "Old", 3).0, C::ClassName);
    }

    #[test]
    fn unsaved_text_is_classified_as_typed() {
        let compiled = "class C { int f; void M() { } }\n";
        let semantic = compile(&[("C.cs", compiled)], false).expect("compiled");
        let typed = "class C { int f; void M() { var x = f; x = 2; } }\n";
        let found = classified(&semantic, typed);
        let (class, modifiers) = class_of(&found, "x", 0);
        assert_eq!(class, SemanticClass::LocalName);
        assert!(modifiers.contains(SemanticModifiers::REASSIGNED));
        assert_eq!(class_of(&found, "f", 1).0, SemanticClass::FieldName);
    }

    #[test]
    fn a_window_of_a_large_file_is_cheap() {
        use std::fmt::Write;
        let mut text = String::from("using System;\nnamespace Big {\n");
        let mut class = 0;
        while text.lines().count() < 2000 {
            let _ = write!(
                text,
                "  class Worker{class} {{\n    int count;\n    static readonly string Name = \"w{class}\";\n\
                 \x20   public int Run(int limit) {{\n      var total = 0;\n      for (var i = 0; i < limit; i++) {{\n\
                 \x20       total += Step(i) + count;\n      }}\n      count = total;\n      return total;\n    }}\n\
                 \x20   int Step(int x) => x * 2 + Name.Length;\n  }}\n"
            );
            class += 1;
        }
        text.push_str("}\n");
        let semantic = compile(&[("C.cs", &text)], false).expect("compiled");
        let lines: Vec<usize> = text.match_indices('\n').map(|(at, _)| at).collect();
        let range = TextSpan::from_bounds(lines[1000] as u32, lines[1100] as u32);
        let started = std::time::Instant::now();
        let found = semantic
            .semantic_tokens(Path::new("/p/C.cs"), range, None)
            .expect("classified");
        let cold = started.elapsed();
        let started = std::time::Instant::now();
        let again = semantic
            .semantic_tokens(Path::new("/p/C.cs"), range, None)
            .expect("classified");
        let warm = started.elapsed();
        eprintln!(
            "100 lines of {}: {} names, {cold:?} cold, {warm:?} warm",
            lines.len(),
            found.len()
        );
        assert_eq!(found, again);
        assert!(found.len() > 150, "{}", found.len());
        assert!(
            found
                .iter()
                .any(|token| token.class == SemanticClass::MethodName),
            "{found:?}"
        );
        // Generous for a shared machine; the figure it prints is the point.
        assert!(cold.as_millis() < 500, "{cold:?}");
    }
}
