//! Which keywords can be written where the cursor is: Roslyn's keyword
//! recommenders, one question per place rather than one per keyword.
//!
//! A keyword offered where it cannot go is worse than one missing: it sorts
//! among the names and gets committed by accident. So the list is built up
//! from the positions [`Code`] says hold — a statement, an expression, a
//! member — and then narrowed by what is around them: `await` only in an
//! `async` body, `break` only in a loop or a `switch`, `base` only in an
//! instance member of a class, a modifier not twice.

use rustlyn_syntax::{SyntaxKind as K, SyntaxNode, SyntaxToken};

use super::context::{Code, is_type_declaration};

/// The built-in types, by keyword.
pub(super) const PREDEFINED_TYPES: &[&str] = &[
    "bool", "byte", "char", "decimal", "double", "float", "int", "long", "nint", "nuint", "object",
    "sbyte", "short", "string", "uint", "ulong", "ushort",
];

/// What the code around the cursor allows, beyond its position.
#[derive(Default, Debug)]
pub(super) struct Surroundings {
    /// In a member or function marked `async`, or at the top level.
    pub is_async: bool,
    /// In a static member, a static class, or a static local function or
    /// lambda: no `this`, no instance members.
    pub is_static: bool,
    /// In a loop: `continue` and `break`.
    pub in_loop: bool,
    /// In a `switch` section: `break`, `case` and `default`.
    pub in_switch: bool,
    /// In a class, where `base` means something.
    pub in_class: bool,
    /// In some type at all, where `this` means something.
    pub in_type: bool,
    /// In a method, an accessor or an operator, where `yield` can go (not
    /// in a lambda).
    pub in_iterator_candidate: bool,
    /// The statement that ends at the cursor is an `if` without an `else`.
    pub after_if: bool,
    /// The statement that ends at the cursor is a `try`: `catch` and
    /// `finally` can follow, and whether it has its `finally` yet.
    pub after_try: Option<bool>,
    /// The type the cursor is in is an interface, a struct, or a static class.
    pub container: Container,
    /// At the very top of a file or namespace, before anything but other
    /// `using`s: where a `using` directive can still go.
    pub usings_allowed: bool,
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Container {
    #[default]
    Class,
    Struct,
    Interface,
    Record,
}

impl Surroundings {
    /// Reads what is around `target` (or the start of the file).
    pub(super) fn of(target: Option<&SyntaxToken>) -> Self {
        let mut found = Self::default();
        let Some(target) = target else {
            found.is_async = true;
            found.usings_allowed = true;
            return found;
        };
        let parent = target.parent().clone();
        let mut in_function = false;
        let mut static_decided = false;
        let mut async_decided = false;
        for node in std::iter::once(parent.clone()).chain(parent.ancestors()) {
            let kind = node.kind();
            let has = |word: &str| node.child_tokens().any(|token| token.text() == word);
            match kind {
                K::WhileStatement
                | K::DoStatement
                | K::ForStatement
                | K::ForEachStatement
                | K::ForEachVariableStatement
                    if !in_function =>
                {
                    // The header of a loop is not in the loop.
                    let body_started = node
                        .child_token_of_kind(K::CloseParenToken)
                        .is_none_or(|close| close.span().end() <= target.span().end())
                        || kind == K::DoStatement;
                    if body_started {
                        found.in_loop = true;
                    }
                }
                K::SwitchSection if !in_function => found.in_switch = true,
                K::ParenthesizedLambdaExpression
                | K::SimpleLambdaExpression
                | K::AnonymousMethodExpression
                | K::LocalFunctionStatement => {
                    if !async_decided {
                        found.is_async = has("async");
                        async_decided = true;
                    }
                    if !static_decided && has("static") {
                        found.is_static = true;
                        static_decided = true;
                    }
                    if kind == K::LocalFunctionStatement && !in_function {
                        found.in_iterator_candidate = true;
                    }
                    in_function = true;
                }
                K::MethodDeclaration
                | K::OperatorDeclaration
                | K::ConversionOperatorDeclaration
                | K::ConstructorDeclaration
                | K::DestructorDeclaration
                | K::PropertyDeclaration
                | K::IndexerDeclaration
                | K::EventDeclaration
                | K::FieldDeclaration
                | K::EventFieldDeclaration => {
                    if !async_decided {
                        found.is_async = has("async");
                        async_decided = true;
                    }
                    if !static_decided {
                        found.is_static = has("static") || has("const");
                        static_decided = true;
                    }
                    if !in_function
                        && matches!(
                            kind,
                            K::MethodDeclaration
                                | K::OperatorDeclaration
                                | K::ConversionOperatorDeclaration
                                | K::PropertyDeclaration
                                | K::IndexerDeclaration
                        )
                    {
                        found.in_iterator_candidate = true;
                    }
                    in_function = true;
                }
                kind if is_type_declaration(kind) => {
                    found.in_type = true;
                    if !found.in_class {
                        found.in_class = matches!(kind, K::ClassDeclaration | K::RecordDeclaration);
                        found.container = match kind {
                            K::StructDeclaration | K::RecordStructDeclaration => Container::Struct,
                            K::InterfaceDeclaration => Container::Interface,
                            K::RecordDeclaration => Container::Record,
                            _ => Container::Class,
                        };
                        if has("static") && !static_decided {
                            found.is_static = true;
                        }
                    }
                    break;
                }
                K::GlobalStatement => {
                    if !async_decided {
                        found.is_async = true;
                        async_decided = true;
                    }
                    static_decided = true;
                }
                _ => {}
            }
        }

        // The statement that ends at the target.
        for node in std::iter::once(parent.clone()).chain(parent.ancestors()) {
            let ends_here = node
                .last_token()
                .is_some_and(|last| last.span() == target.span());
            if !ends_here {
                break;
            }
            match node.kind() {
                K::IfStatement if node.child_of_kind(K::ElseClause).is_none() => {
                    found.after_if = true;
                }
                K::TryStatement => {
                    found.after_try = Some(node.child_of_kind(K::FinallyClause).is_some());
                }
                _ => {}
            }
        }

        // Only `using`s and `extern alias`es before the target.
        let container = parent
            .ancestors()
            .chain(std::iter::once(parent.clone()))
            .find(|node| {
                matches!(
                    node.kind(),
                    K::CompilationUnit
                        | K::NamespaceDeclaration
                        | K::FileScopedNamespaceDeclaration
                )
            });
        found.usings_allowed = container.is_some_and(|container| {
            container
                .children()
                .filter(|child| child.span().end() <= target.span().end())
                .all(|child| {
                    matches!(
                        child.kind(),
                        K::UsingDirective | K::ExternAliasDirective | K::AttributeList
                    ) || child.kind().is_type_node()
                })
        });
        found
    }
}

/// The keywords for `code`, in no particular order.
#[allow(clippy::too_many_lines)] // a table, read top to bottom
pub(super) fn keywords(code: &Code, around: &Surroundings) -> Vec<&'static str> {
    let mut words: Vec<&'static str> = Vec::new();

    if code.statement {
        words.extend([
            "if",
            "for",
            "foreach",
            "while",
            "do",
            "switch",
            "try",
            "return",
            "throw",
            "goto",
            "using",
            "lock",
            "checked",
            "unchecked",
            "unsafe",
            "fixed",
            "const",
            "var",
            "ref",
            "scoped",
            "static",
            "void",
        ]);
        if around.is_async {
            words.push("await");
        }
        words.push("async");
        if around.in_loop || around.in_switch {
            words.push("break");
        }
        if around.in_loop {
            words.push("continue");
        }
        if around.in_switch {
            words.extend(["case", "default"]);
        }
        if around.in_iterator_candidate {
            words.push("yield");
        }
        if around.after_if {
            words.push("else");
        }
        if let Some(has_finally) = around.after_try {
            words.push("catch");
            if !has_finally {
                words.push("finally");
            }
        }
        words.extend(PREDEFINED_TYPES);
    }
    if code.global {
        words.extend([
            "class",
            "struct",
            "interface",
            "enum",
            "delegate",
            "record",
            "namespace",
        ]);
    }
    if code.expression {
        words.extend([
            "new",
            "true",
            "false",
            "null",
            "default",
            "typeof",
            "nameof",
            "sizeof",
            "checked",
            "unchecked",
            "delegate",
            "stackalloc",
        ]);
        if around.in_type && !around.is_static && around.container != Container::Interface {
            words.push("this");
            if around.in_class {
                words.push("base");
            }
        }
        if around.is_async {
            words.push("await");
        }
        words.extend(["async", "static"]);
        if code.allows_var {
            words.push("var");
        }
        if code.argument {
            words.extend(["out", "ref", "in"]);
        }
        if code.pattern {
            words.extend(["not", "var"]);
        }
        words.extend(PREDEFINED_TYPES);
    }
    if code.type_only {
        if code.constraint {
            words.extend(["class", "struct", "new", "unmanaged", "notnull", "default"]);
        } else if !code.base_list {
            words.extend(PREDEFINED_TYPES);
            if !code.after_new {
                words.push("dynamic");
            }
        }
        if code.allows_var {
            words.push("var");
        }
        if code.allows_void {
            words.push("void");
        }
        if code.parameter {
            words.extend(["ref", "out", "in", "params", "this", "scoped", "readonly"]);
        }
        // Modifiers of a local or a local function: `static |`.
        if !code.modifiers.is_empty() {
            words.extend(local_modifiers(&code.modifiers));
        }
    }
    if code.member {
        words.extend(member_keywords(&code.modifiers, around.container));
    }
    if code.type_declaration {
        words.extend(type_declaration_keywords(
            &code.modifiers,
            around.usings_allowed,
        ));
    }
    if let Some(list) = &code.accessors {
        words.extend(accessor_keywords(list));
    }
    if code.after_expression {
        words.extend(["is", "as", "switch", "with"]);
    }
    if code.foreach_in {
        words.push("in");
    }
    if code.where_clause {
        words.push("where");
    }
    if code.switch_labels {
        words.extend(["case", "default"]);
    }

    words.sort_unstable();
    words.dedup();
    words
}

const ACCESSIBILITY: &[&str] = &["public", "private", "protected", "internal"];

/// Whether `word` can join `written` in front of the same declaration.
fn joins(word: &str, written: &[String]) -> bool {
    if written.iter().any(|w| w == word) {
        return false;
    }
    let has = |w: &str| written.iter().any(|x| x == w);
    if ACCESSIBILITY.contains(&word) {
        let accessibility: Vec<&String> = written
            .iter()
            .filter(|w| ACCESSIBILITY.contains(&w.as_str()))
            .collect();
        return match accessibility.as_slice() {
            [] => true,
            // `protected internal`, `private protected`.
            [one] => matches!(
                (one.as_str(), word),
                ("protected", "internal" | "private") | ("internal" | "private", "protected")
            ),
            _ => false,
        };
    }
    match word {
        "virtual" | "abstract" | "override" | "sealed" => {
            !(has("static") || has("const") || (word == "sealed" && has("abstract")))
        }
        "static" => !has("virtual") && !has("abstract") && !has("override") && !has("const"),
        "const" => !has("static") && !has("readonly"),
        _ => !has("const"),
    }
}

fn member_keywords(written: &[String], container: Container) -> Vec<&'static str> {
    let mut words: Vec<&'static str> = Vec::new();
    let candidates: &[&'static str] = match container {
        Container::Interface => &[
            "public",
            "private",
            "protected",
            "internal",
            "static",
            "abstract",
            "virtual",
            "sealed",
            "partial",
            "extern",
            "unsafe",
            "new",
            "event",
        ],
        Container::Struct => &[
            "public", "private", "internal", "static", "readonly", "const", "override", "extern",
            "unsafe", "volatile", "new", "partial", "async", "required", "event", "implicit",
            "explicit", "fixed",
        ],
        Container::Class | Container::Record => &[
            "public",
            "private",
            "protected",
            "internal",
            "static",
            "readonly",
            "const",
            "virtual",
            "override",
            "abstract",
            "sealed",
            "extern",
            "unsafe",
            "volatile",
            "new",
            "partial",
            "async",
            "required",
            "event",
            "implicit",
            "explicit",
        ],
    };
    for &word in candidates {
        if joins(word, written) {
            words.push(word);
        }
    }
    if !written.iter().any(|w| w == "const") {
        words.push("void");
    }
    words.extend(PREDEFINED_TYPES);
    words.push("dynamic");
    if !written.iter().any(|w| {
        matches!(
            w.as_str(),
            "virtual" | "override" | "const" | "readonly" | "volatile" | "async" | "required"
        )
    }) {
        words.extend(["class", "struct", "interface", "enum", "delegate", "record"]);
    }
    words
}

fn type_declaration_keywords(written: &[String], usings_allowed: bool) -> Vec<&'static str> {
    let mut words: Vec<&'static str> = Vec::new();
    for word in [
        "public", "internal", "static", "abstract", "sealed", "partial", "unsafe", "file",
        "readonly", "ref",
    ] {
        if written.iter().any(|w| w == word) {
            continue;
        }
        if ACCESSIBILITY.contains(&word)
            && written
                .iter()
                .any(|w| ACCESSIBILITY.contains(&w.as_str()) || w == "file")
        {
            continue;
        }
        words.push(word);
    }
    words.extend(["class", "struct", "interface", "enum", "delegate", "record"]);
    if written.is_empty() {
        words.push("namespace");
        if usings_allowed {
            words.extend(["using", "extern", "global"]);
        }
    }
    words
}

fn local_modifiers(written: &[String]) -> Vec<&'static str> {
    ["static", "async", "unsafe", "extern", "const", "readonly"]
        .into_iter()
        .filter(|word| !written.iter().any(|w| w == word))
        .filter(|&word| {
            // `const` stands alone; the others start a local function.
            if written.iter().any(|w| w == "const") {
                false
            } else {
                word != "const" && word != "readonly"
            }
        })
        .collect()
}

fn accessor_keywords(list: &SyntaxNode) -> Vec<&'static str> {
    let is_event = list
        .parent()
        .is_some_and(|declaration| declaration.kind() == K::EventDeclaration);
    let written: Vec<String> = list
        .children()
        .filter_map(|accessor| {
            accessor
                .child_tokens()
                .find(|token| matches!(token.text(), "get" | "set" | "init" | "add" | "remove"))
                .map(|token| token.text().to_string())
        })
        .collect();
    let has = |word: &str| written.iter().any(|w| w == word);
    let mut words = Vec::new();
    if is_event {
        for word in ["add", "remove"] {
            if !has(word) {
                words.push(word);
            }
        }
        return words;
    }
    if !has("get") {
        words.push("get");
    }
    if !has("set") && !has("init") {
        words.extend(["set", "init"]);
    }
    words.extend(["private", "protected", "internal", "readonly"]);
    words
}
