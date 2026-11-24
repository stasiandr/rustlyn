//! What changed in a file between the compilation an editor has loaded and
//! the one just made: by the identity of each declaration (what it is, whose
//! it is, its name and parameter types), not by where it stands.

use std::collections::{BTreeMap, HashSet};

use rustlyn_semantics::{
    Binder, Compilation, Diagnostics, MethodKind, Modifiers, SymbolId, SymbolKind,
};
use rustlyn_syntax::{SyntaxKind, SyntaxNode};
use rustlyn_text::TextSpan;

/// One declaration of a file.
struct Declaration {
    symbol: SymbolId,
    kind: Kind,
    /// Its text without its body: what has to stay the same for the change
    /// to be a body's alone.
    head: String,
    body: String,
    /// Its body's tokens, without what lies between them: an edit of
    /// spaces, line breaks or comments alone changes nothing that runs.
    tokens: String,
    /// A type's base type and interfaces, as written.
    bases: Vec<String>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Type,
    Method,
    Field,
    /// A property, not an indexer: its accessors are compared as methods.
    Property,
    Other,
}

/// What a file's edits come to, in the new compilation's symbols.
#[derive(Default)]
pub(crate) struct Changes {
    /// Methods whose body changed — and properties written `int P => e;`,
    /// whose declaration is their getter.
    pub(crate) bodies: Vec<SymbolId>,
    /// The key of each of `bodies`, which outlives the compilation.
    pub(crate) body_keys: Vec<String>,
    /// Methods, fields and types the loaded assembly does not have.
    pub(crate) added_methods: Vec<SymbolId>,
    pub(crate) added_fields: Vec<SymbolId>,
    pub(crate) added_types: Vec<SymbolId>,
    /// Properties the loaded assembly lacks: `{ get; set; }` ones are kept
    /// as fields are; ones with a getter of their own are read through it.
    pub(crate) added_properties: Vec<SymbolId>,
    /// Added methods named as a method the type had: an overload, or one
    /// whose signature changed. Code elsewhere that calls the old one was
    /// compiled against it and keeps calling it.
    pub(crate) reshaped: Vec<SymbolId>,
    /// Static fields whose initializer changed, their type not: the patch
    /// gives the loaded field the new value once, and every reader sees it.
    pub(crate) reinitialized: Vec<SymbolId>,
    /// Static constructors whose body changed: run once more, as written now.
    pub(crate) rerun: Vec<SymbolId>,
    /// Constants given another value: every method that reads one had it
    /// written into it, and is patched with the new one.
    pub(crate) reconstants: Vec<SymbolId>,
    /// Serialized fields of a Unity object given another type: kept beside
    /// it as a changed field is, first made from what the loaded field holds.
    pub(crate) converted: Vec<SymbolId>,
    /// Added fields a constructor gives a value: the field, the constructor,
    /// and the span of the assignment. An object made before the patch never
    /// ran it, so the field takes that value the first time it is read.
    pub(crate) assigned: Vec<(SymbolId, SymbolId, TextSpan)>,
}

impl Changes {
    pub(crate) fn extend(&mut self, other: Self) {
        self.bodies.extend(other.bodies);
        self.body_keys.extend(other.body_keys);
        self.added_methods.extend(other.added_methods);
        self.added_fields.extend(other.added_fields);
        self.added_types.extend(other.added_types);
        self.added_properties.extend(other.added_properties);
        self.reshaped.extend(other.reshaped);
        self.reinitialized.extend(other.reinitialized);
        self.rerun.extend(other.rerun);
        self.converted.extend(other.converted);
        self.reconstants.extend(other.reconstants);
        self.assigned.extend(other.assigned);
    }
}

/// The qualified name of every type a compilation declares in source.
pub(crate) fn type_names(compilation: &Compilation) -> HashSet<String> {
    let symbols = compilation.symbols();
    compilation
        .all_types()
        .filter(|ty| !compilation.is_from_metadata(ty.id))
        .map(|ty| symbols.qualified_name(ty.id))
        .collect()
}

/// How the file at `path` differs between `before` and `after`, or why the
/// difference is one only a reload can bring in. `known` holds the types
/// `before` declares anywhere: a part of one that turns up in a new file —
/// what a generator writes for a type it had not written for — adds members
/// to it, not a type.
pub(crate) fn changes(
    before: &Compilation,
    after: &Compilation,
    path: &str,
    known: &HashSet<String>,
    patched: &HashSet<String>,
) -> Result<Changes, String> {
    let mut old = declarations(before, path);
    let new = declarations(after, path);
    let mut changes = Changes::default();
    for (key, declaration) in &new {
        if declaration.kind == Kind::Type && !old.contains_key(key) && known.contains(key) {
            old.insert(
                key.clone(),
                Declaration {
                    symbol: declaration.symbol,
                    kind: Kind::Type,
                    head: declaration.head.clone(),
                    body: String::new(),
                    tokens: String::new(),
                    bases: declaration.bases.clone(),
                },
            );
        }
    }
    // Members of a type the loaded assembly lacks come with the type, and
    // the accessors of a property with the property.
    let added_types: Vec<String> = new
        .iter()
        .filter(|(key, declaration)| {
            matches!(declaration.kind, Kind::Type | Kind::Property) && !old.contains_key(*key)
        })
        .map(|(key, _)| key.clone())
        .collect();
    let mut constructors: Vec<(SymbolId, String)> = Vec::new();
    let mut refielded: Vec<String> = Vec::new();
    for (key, declaration) in &new {
        if added_types
            .iter()
            .any(|ty| key != ty && key.starts_with(&format!("{ty}.")))
        {
            continue;
        }
        match (old.get(key), declaration.kind) {
            (None, Kind::Type) => changes.added_types.push(declaration.symbol),
            (None, Kind::Method) => {
                changes.added_methods.push(declaration.symbol);
                let stem = key.split('(').next().unwrap_or(key);
                if old.keys().any(|was| was.split('(').next() == Some(stem)) {
                    changes.reshaped.push(declaration.symbol);
                }
            }
            (None, Kind::Field) => changes.added_fields.push(declaration.symbol),
            (None, Kind::Property) => changes.added_properties.push(declaration.symbol),
            (None, Kind::Other) => {
                return Err(format!(
                    "{key} is new, and only methods, fields and types are patched"
                ));
            }
            // A field given another type or initializer is a new field to
            // the code that uses it: kept beside the object, as an added one
            // is, with the old one left to what no edit touched. Unity's
            // serializer and the Inspector see only the old one.
            (Some(was), Kind::Field)
                if was.head != declaration.head
                    && after
                        .symbols()
                        .get(declaration.symbol)
                        .modifiers
                        .contains(Modifiers::CONST)
                    && type_text(before, was.symbol) == type_text(after, declaration.symbol) =>
            {
                changes.added_fields.push(declaration.symbol);
                changes.reconstants.push(declaration.symbol);
            }
            (Some(was), Kind::Field)
                if was.head != declaration.head
                    && after
                        .symbols()
                        .get(declaration.symbol)
                        .modifiers
                        .contains(Modifiers::STATIC)
                    && !after
                        .symbols()
                        .get(declaration.symbol)
                        .modifiers
                        .contains(Modifiers::CONST)
                    && type_text(before, was.symbol) == type_text(after, declaration.symbol) =>
            {
                changes.reinitialized.push(declaration.symbol);
            }
            (Some(was), Kind::Field) if was.head != declaration.head => {
                let symbol = after.symbols().get(declaration.symbol);
                let marked = after
                    .declaration_node(declaration.symbol)
                    .is_some_and(|node| {
                        node.parent()
                            .and_then(|list| list.parent().map(|field| field.text()))
                            .is_some_and(|text| text.contains("SerializeField"))
                    });
                let serialized = marked
                    || (symbol.accessibility == rustlyn_semantics::Accessibility::Public
                        && !symbol.modifiers.contains(Modifiers::STATIC));
                // A serialized field's initializer is what a new object
                // starts with before its data is read: an object already
                // made has its data, and nothing changes for it.
                let same_type =
                    type_text(before, was.symbol) == type_text(after, declaration.symbol);
                if serialized && same_type {
                    continue;
                }
                // Given another type on a Unity object, it takes what the
                // loaded field holds, converted: a component from a game
                // object, a game object from a component, a number.
                if marked || (serialized && unity_object(after, symbol.container)) {
                    changes.added_fields.push(declaration.symbol);
                    changes.converted.push(declaration.symbol);
                    changes.reshaped.push(declaration.symbol);
                    refielded.push(symbol.name.clone());
                    continue;
                }
                if serialized || symbol.modifiers.contains(Modifiers::CONST) {
                    return Err(format!(
                        "{key}: its declaration changed, and what serializes it or reads it as a constant sees the old one"
                    ));
                }
                changes.added_fields.push(declaration.symbol);
                changes.reshaped.push(declaration.symbol);
                refielded.push(symbol.name.clone());
            }
            // A field that became a property kept as storage: new storage,
            // first the old field's value, read by whoever names it in the
            // file.
            (Some(was), Kind::Property)
                if was.kind == Kind::Field
                    && super::patch::is_stored(after, declaration.symbol) =>
            {
                let symbol = after.symbols().get(declaration.symbol);
                changes.added_properties.push(declaration.symbol);
                changes.converted.push(declaration.symbol);
                changes.reshaped.push(declaration.symbol);
                refielded.push(symbol.name.clone());
            }
            // A method that became static or stopped being, or a generic one
            // whose body changed: a new method of the patch, which every
            // method of the file that calls it is patched to call. A file the
            // edit did not touch that calls the old one makes it a reload.
            (Some(was), Kind::Method)
                if (was.head != declaration.head
                    && squeeze_static(&was.head) == squeeze_static(&declaration.head))
                    || (was.tokens != declaration.tokens
                        && after
                            .symbols()
                            .get(declaration.symbol)
                            .as_method()
                            .is_some_and(|method| !method.type_parameters.is_empty())) =>
            {
                changes.added_methods.push(declaration.symbol);
                changes.reshaped.push(declaration.symbol);
                refielded.push(after.symbols().get(declaration.symbol).name.clone());
            }
            (Some(was), _) if was.head != declaration.head => {
                return Err(format!("{key}: its declaration changed, not only its body"));
            }
            // An interface the edit took away is still the loaded type's,
            // which is harmless; one it added is not there to be called
            // through.
            (Some(was), Kind::Type)
                if declaration
                    .bases
                    .iter()
                    .any(|base| !was.bases.contains(base)) =>
            {
                return Err(format!("{key}: a base type or interface was added"));
            }
            // A method patched before is patched again, even back to what
            // the loaded assembly has: the editor still jumps to the patch.
            (Some(was), Kind::Method)
                if was.tokens == declaration.tokens && patched.contains(key) =>
            {
                changes.bodies.push(declaration.symbol);
                changes.body_keys.push(key.clone());
            }
            (Some(was), Kind::Property)
                if was.tokens == declaration.tokens
                    && patched.contains(key)
                    && declaration.body.trim_start().starts_with("=>") =>
            {
                changes.bodies.push(declaration.symbol);
                changes.body_keys.push(key.clone());
            }
            (Some(was), Kind::Method) if was.tokens != declaration.tokens => {
                let symbols = after.symbols();
                let struct_owner = symbols
                    .get(declaration.symbol)
                    .container
                    .is_some_and(|owner| {
                        symbols.get(owner).type_kind() == Some(rustlyn_semantics::TypeKind::Struct)
                    });
                if symbols
                    .get(declaration.symbol)
                    .as_method()
                    .is_some_and(|method| method.method_kind == MethodKind::Constructor)
                    && !struct_owner
                    && !super::patch::patchable_constructor(after, declaration.symbol)
                {
                    constructors.push((declaration.symbol, was.body.clone()));
                } else if after
                    .symbols()
                    .get(declaration.symbol)
                    .as_method()
                    .is_some_and(|method| method.method_kind == MethodKind::StaticConstructor)
                {
                    changes.rerun.push(declaration.symbol);
                } else {
                    changes.bodies.push(declaration.symbol);
                    changes.body_keys.push(key.clone());
                }
            }
            // `int P => x;` has no accessor of its own: the property is its
            // getter.
            (Some(was), Kind::Property)
                if was.tokens != declaration.tokens
                    && declaration.body.trim_start().starts_with("=>") =>
            {
                changes.bodies.push(declaration.symbol);
                changes.body_keys.push(key.clone());
            }
            _ => {}
        }
    }
    // Every method of the file that names a field given new storage reads
    // the new one, its body changed or not.
    let word = |byte: u8| byte.is_ascii_alphanumeric() || byte == b'_';
    let names = |body: &str, name: &str| {
        body.match_indices(name).any(|(at, _)| {
            let bytes = body.as_bytes();
            !at.checked_sub(1).is_some_and(|index| word(bytes[index]))
                && !bytes.get(at + name.len()).is_some_and(|&byte| word(byte))
        })
    };
    for (key, declaration) in &new {
        if declaration.kind == Kind::Method
            && !changes.bodies.contains(&declaration.symbol)
            && !changes.added_methods.contains(&declaration.symbol)
            && refielded.iter().any(|name| names(&declaration.body, name))
            && !after
                .symbols()
                .get(declaration.symbol)
                .as_method()
                .is_some_and(|method| method.method_kind == MethodKind::Constructor)
        {
            changes.bodies.push(declaration.symbol);
            changes.body_keys.push(key.clone());
        }
    }
    // A class's constructor no patch can carry — a generic type's — need
    // not be one when it only gives added fields their values: those values
    // come when the fields are first read.
    for (constructor, was) in constructors {
        let assigned = field_assignments(after, constructor, &changes.added_fields);
        let node = after
            .declaration_node(constructor)
            .ok_or("a constructor without its declaration")?;
        let body = node
            .children()
            .find(|child| child.kind() == SyntaxKind::Block)
            .ok_or("a constructor without a body")?;
        let mut rest = body.text();
        for &(_, statement) in assigned.iter().rev() {
            let from = (statement.start() - body.span().start()) as usize;
            rest.replace_range(from..from + statement.length() as usize, "");
        }
        let squeeze = |text: &str| text.split_whitespace().collect::<String>();
        if squeeze(&rest) != squeeze(&was) {
            let generic = after
                .symbols()
                .get(constructor)
                .container
                .is_some_and(|owner| super::patch::generic_around(after, owner));
            let why = if generic {
                "a generic type's constructor"
            } else {
                "a constructor no patch can carry"
            };
            return Err(format!(
                "{}: {why} needs a reload when it does more than give added fields their values",
                after.symbols().qualified_name(constructor)
            ));
        }
        for (field, statement) in assigned {
            changes.assigned.push((field, constructor, statement));
        }
    }
    Ok(changes)
}

/// The statements of a constructor's body that give an added field its
/// value — `field = value;` or `this.field = value;` — by the field and the
/// statement's span, in order.
fn field_assignments(
    compilation: &Compilation,
    constructor: SymbolId,
    added: &[SymbolId],
) -> Vec<(SymbolId, TextSpan)> {
    let symbols = compilation.symbols();
    let owner = symbols.get(constructor).container;
    let Some(body) = compilation.declaration_node(constructor).and_then(|node| {
        node.children()
            .find(|child| child.kind() == SyntaxKind::Block)
    }) else {
        return Vec::new();
    };
    let mut found = Vec::new();
    for statement in body.children() {
        if statement.kind() != SyntaxKind::ExpressionStatement {
            continue;
        }
        let Some(assignment) = statement
            .children()
            .find(|child| child.kind() == SyntaxKind::SimpleAssignmentExpression)
        else {
            continue;
        };
        let Some(left) = assignment.children().next() else {
            continue;
        };
        let name = match left.kind() {
            SyntaxKind::IdentifierName => left.text(),
            SyntaxKind::SimpleMemberAccessExpression
                if left
                    .children()
                    .next()
                    .is_some_and(|receiver| receiver.kind() == SyntaxKind::ThisExpression) =>
            {
                left.children()
                    .last()
                    .map(|member| member.text())
                    .unwrap_or_default()
            }
            _ => continue,
        };
        if let Some(&field) = added.iter().find(|&&field| {
            symbols.get(field).name == name.trim() && symbols.get(field).container == owner
        }) {
            found.push((field, statement.span()));
        }
    }
    found
}

/// Every declaration of the file, by its identity.
fn declarations(compilation: &Compilation, path: &str) -> BTreeMap<String, Declaration> {
    let mut found = BTreeMap::new();
    let trees = compilation.trees();
    let Some(index) = (0..trees.len()).find(|&index| {
        trees
            .source(index)
            .is_some_and(|source| source.name() == path)
    }) else {
        return found;
    };
    let Some(tree) = trees.get(index) else {
        return found;
    };
    let binder = Binder::new(compilation);
    let symbols = compilation.symbols();
    for node in tree.root().descendants() {
        let kind = match node.kind() {
            SyntaxKind::ClassDeclaration
            | SyntaxKind::StructDeclaration
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::EnumDeclaration
            | SyntaxKind::RecordDeclaration
            | SyntaxKind::RecordStructDeclaration
            | SyntaxKind::DelegateDeclaration => Kind::Type,
            SyntaxKind::MethodDeclaration
            | SyntaxKind::ConstructorDeclaration
            | SyntaxKind::DestructorDeclaration
            | SyntaxKind::OperatorDeclaration
            | SyntaxKind::ConversionOperatorDeclaration
            | SyntaxKind::GetAccessorDeclaration
            | SyntaxKind::SetAccessorDeclaration
            | SyntaxKind::InitAccessorDeclaration
            | SyntaxKind::AddAccessorDeclaration
            | SyntaxKind::RemoveAccessorDeclaration => Kind::Method,
            SyntaxKind::VariableDeclarator
                if node
                    .parent()
                    .and_then(SyntaxNode::parent)
                    .is_some_and(|holder| holder.kind() == SyntaxKind::FieldDeclaration) =>
            {
                Kind::Field
            }
            SyntaxKind::EnumMemberDeclaration => Kind::Field,
            SyntaxKind::PropertyDeclaration => Kind::Property,
            SyntaxKind::IndexerDeclaration
            | SyntaxKind::EventDeclaration
            | SyntaxKind::EventFieldDeclaration => Kind::Other,
            _ => continue,
        };
        let Some(symbol) = compilation.declared_symbol(index, node.span()) else {
            continue;
        };
        let (head, body) = split(&node, kind);
        let tokens = body_tokens(&node, kind, &body);
        let head = without_attributes(&node, head);
        // What the loaded code depends on, and nothing else: not attributes,
        // nor who may call it (the editor's build opens every member), nor
        // how the text is laid out — nor, for a method, its parameters'
        // names, while its key holds their types.
        let (head, bases) = match kind {
            Kind::Method => {
                let modifiers = symbols.get(symbol).modifiers;
                let mut kept: Vec<&str> = [
                    (Modifiers::STATIC, "static"),
                    (Modifiers::ABSTRACT, "abstract"),
                    (Modifiers::SEALED, "sealed"),
                    (Modifiers::VIRTUAL, "virtual"),
                    (Modifiers::OVERRIDE, "override"),
                    (Modifiers::EXTERN, "extern"),
                    (Modifiers::NEW, "new"),
                    (Modifiers::READONLY, "readonly"),
                ]
                .iter()
                .filter(|(flag, _)| modifiers.contains(*flag))
                .map(|(_, word)| *word)
                .collect();
                let constraints: Vec<String> = node
                    .children()
                    .filter(|child| child.kind() == SyntaxKind::TypeParameterConstraintClause)
                    .map(|clause| essential(&clause.text()))
                    .collect();
                kept.extend(constraints.iter().map(String::as_str));
                (kept.join(" "), Vec::new())
            }
            Kind::Type => {
                let list = node
                    .children()
                    .find(|child| child.kind() == SyntaxKind::BaseList);
                let bases: Vec<String> = list
                    .iter()
                    .flat_map(SyntaxNode::children)
                    .map(|base| essential(&base.text()))
                    .collect();
                let head = match &list {
                    Some(list) => head.replace(list.text().trim(), ""),
                    None => head,
                };
                (essential(&head), bases)
            }
            _ => (essential(&head), Vec::new()),
        };
        let mut key = symbols.qualified_name(symbol);
        if symbols.get(symbol).kind == SymbolKind::Method
            && let Some(method) = symbols.get(symbol).as_method()
        {
            let parameters: Vec<String> = method
                .parameters
                .iter()
                .map(|parameter| {
                    binder
                        .type_of(*parameter, &mut Diagnostics::new())
                        .display(symbols)
                })
                .collect();
            // What it returns is part of what a caller was compiled against.
            let returns = binder
                .type_of(symbol, &mut Diagnostics::new())
                .display(symbols);
            key = format!("{key}({}){returns}", parameters.join(","));
        }
        found.insert(
            key,
            Declaration {
                symbol,
                kind,
                head,
                body,
                tokens,
                bases,
            },
        );
    }
    found
}

/// A declaration's text as far as what it declares goes: without
/// accessibility, and with its spacing made one. (Its attribute lists are
/// taken out before, by `without_attributes`.)
fn essential(text: &str) -> String {
    let out = text;
    let words: Vec<&str> = out
        .split_whitespace()
        .filter(|word| !matches!(*word, "public" | "private" | "protected" | "internal"))
        .collect();
    // One space between two words, none beside punctuation.
    let mut squeezed = String::new();
    for word in words {
        let joins = squeezed
            .chars()
            .last()
            .is_some_and(|last| last.is_alphanumeric() || last == '_')
            && word
                .chars()
                .next()
                .is_some_and(|first| first.is_alphanumeric() || first == '_');
        if joins {
            squeezed.push(' ');
        }
        squeezed.push_str(word);
    }
    squeezed
}

/// Whether the type is a Unity object — a `MonoBehaviour`, a
/// `ScriptableObject` — whose serialized fields Unity writes.
fn unity_object(compilation: &Compilation, ty: Option<SymbolId>) -> bool {
    let binder = Binder::new(compilation);
    let symbols = compilation.symbols();
    let mut current = ty;
    for _ in 0..32 {
        let Some(id) = current else { return false };
        if symbols.qualified_name(id) == "UnityEngine.Object" {
            return true;
        }
        current = match binder.base_class_of(id) {
            Some(rustlyn_semantics::Type::Named { symbol, .. }) => Some(symbol),
            _ => None,
        };
    }
    false
}

/// A method's head without `static`: what is left to compare when only
/// that changed.
fn squeeze_static(head: &str) -> String {
    head.split_whitespace()
        .filter(|word| *word != "static")
        .collect::<Vec<_>>()
        .join(" ")
}

/// A symbol's type as the compilation names it.
fn type_text(compilation: &Compilation, symbol: SymbolId) -> String {
    Binder::new(compilation)
        .type_of(symbol, &mut Diagnostics::new())
        .display(compilation.symbols())
}

/// `head` without the text of the attribute lists in `node`.
fn without_attributes(node: &SyntaxNode, mut head: String) -> String {
    for list in node
        .descendants()
        .filter(|inner| inner.kind() == SyntaxKind::AttributeList)
    {
        let text = list.text();
        if let Some(at) = head.find(text.trim()) {
            head.replace_range(at..at + text.trim().len(), " ");
        }
    }
    head
}

/// A declaration's head and its body. A type's head is all of it but its
/// members; a field's is all of it, initializer and all.
/// A method's body as its tokens alone, one space between each two.
fn body_tokens(node: &SyntaxNode, kind: Kind, body: &str) -> String {
    let block = node.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::Block | SyntaxKind::ArrowExpressionClause
        )
    });
    match (kind, block) {
        (Kind::Method, Some(block)) => block
            .descendant_tokens()
            .map(|token| token.text().to_string())
            .collect::<Vec<_>>()
            .join(" "),
        _ => body.to_string(),
    }
}

fn split(node: &SyntaxNode, kind: Kind) -> (String, String) {
    let text = node.text();
    let start = node.span().start() as usize;
    match kind {
        Kind::Method => {
            let body = node.children().find(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::Block | SyntaxKind::ArrowExpressionClause
                )
            });
            match body {
                Some(body) => {
                    let at = body.span().start() as usize - start;
                    (text[..at].trim().to_string(), body.text())
                }
                None => (text.trim().to_string(), String::new()),
            }
        }
        // Up to the opening brace: modifiers, name, bases. Its attributes
        // are not: what a generator reads from them it writes again, and a
        // patch carries what it wrote.
        Kind::Type => {
            let at = node
                .children()
                .take_while(|child| child.kind() == SyntaxKind::AttributeList)
                .last()
                .map_or(0, |list| list.span().end() as usize - start);
            let rest = &text[at..];
            let head = rest.split('{').next().unwrap_or(rest).trim().to_string();
            (head, text[..at].to_string())
        }
        // A field's declarator holds its name and initializer; what it holds
        // is its whole declaration, type included.
        Kind::Field if node.kind() == SyntaxKind::EnumMemberDeclaration => {
            (text.trim().to_string(), String::new())
        }
        Kind::Field => {
            let whole = node
                .parent()
                .and_then(SyntaxNode::parent)
                .map_or_else(|| text.clone(), SyntaxNode::text);
            (whole.trim().to_string(), String::new())
        }
        // A property's accessors are declarations of their own, compared as
        // methods: its head is what stands before them, and the initializer
        // after them, which only a constructor that has run would give.
        Kind::Property | Kind::Other => {
            let at = node
                .children()
                .find(|child| {
                    matches!(
                        child.kind(),
                        SyntaxKind::AccessorList | SyntaxKind::ArrowExpressionClause
                    )
                })
                .map_or(text.len(), |list| list.span().start() as usize - start);
            let mut head = text[..at].trim().to_string();
            if let Some(initializer) = node
                .children()
                .find(|child| child.kind() == SyntaxKind::EqualsValueClause)
            {
                head.push(' ');
                head.push_str(initializer.text().trim());
            }
            (head, text[at..].to_string())
        }
    }
}
