//! Completion the way Roslyn's `CompletionService` does it: a set of
//! providers, each for one kind of place, and a context that says which
//! place the cursor is in.
//!
//! [`context`] reads the token in front of the word being typed and names
//! the place: after a `.`, inside `new C { }`, after `override`, where a new
//! name goes, in a `///` comment, on a `#` line, or plain code with the
//! positions it allows. Then the providers for that place run:
//!
//! * [`keywords`] — only the keywords the grammar allows there.
//! * [`symbols`] — what is in scope, narrowed by the place: types only after
//!   `new` or in a declaration, no instance members in a static one, the
//!   enum's members where an enum is expected, the attribute classes in `[`.
//! * [`overrides`] — `override` and `partial` members, written out.
//! * [`arguments`] — `name:` for the parameters a call has not named yet.
//! * [`initializers`] — the members `new C { }` can still set.
//! * [`imports`] — types and extension methods from namespaces the file does
//!   not import, with the `using` that brings them in.
//! * [`documentation`] and [`directives`] — tags in `///`, and `#` lines.
//! * [`snippets`] and [`names`] — `prop` and `cw`, and names for a new
//!   variable from its type.
//!
//! [`trigger`] is the other half: which typed characters open the list.

mod arguments;
mod context;
mod directives;
mod documentation;
mod imports;
mod initializers;
mod keywords;
mod names;
mod overrides;
mod snippets;
mod symbols;
mod trigger;

use std::collections::HashSet;
use std::path::Path;

use rustlyn_semantics::{SymbolId, SymbolKind};
use rustlyn_syntax::SyntaxKind;

pub(super) use imports::ImportIndex;
pub use trigger::completion_trigger;

use super::{Completion, CompletionKind, Completions, Documentation, Semantic, View};
use context::{Code, Site, Spot};

impl Default for Completion {
    fn default() -> Self {
        Self {
            label: String::new(),
            kind: CompletionKind::Keyword,
            detail: String::new(),
            rank: 0,
            insert_text: None,
            filter_text: None,
            additional_edits: Vec::new(),
            preselect: false,
            commit_characters: String::new(),
            is_snippet: false,
            caret: None,
            symbol: None,
        }
    }
}

impl Completion {
    /// A keyword, sorted after names.
    fn keyword(word: &str) -> Self {
        Self {
            label: word.to_string(),
            kind: CompletionKind::Keyword,
            detail: format!("{word} keyword"),
            rank: 30,
            ..Self::default()
        }
    }

    /// What the item writes: its insert text, or its label.
    #[must_use]
    pub fn text_to_insert(&self) -> &str {
        self.insert_text.as_deref().unwrap_or(&self.label)
    }
}

impl Semantic {
    /// The full description of the completion item labelled `label` at
    /// `offset`: its documentation comment when it is a symbol, its detail
    /// otherwise. What an editor shows beside the selected item.
    #[must_use]
    pub fn completion_description(
        &self,
        path: &Path,
        offset: u32,
        text: Option<&str>,
        label: &str,
    ) -> Option<Documentation> {
        let mut view = self.view_of(path, text)?;
        let list = view.complete(offset);
        let item = list.items.into_iter().find(|item| item.label == label)?;
        let Some(symbol) = item.symbol else {
            return Some(Documentation {
                signature: item.detail,
                ..Documentation::default()
            });
        };
        Some(self.symbol_documentation(symbol))
    }

    /// The documentation of a symbol, the way hovering over it shows it.
    fn symbol_documentation(&self, symbol: SymbolId) -> Documentation {
        let symbols = self.compilation.symbols();
        let container = symbols
            .get(symbol)
            .container
            .filter(|container| !symbols.get(*container).name.is_empty())
            .map(|container| symbols.qualified_name(container))
            .unwrap_or_default();
        let xml = if self.compilation.is_from_metadata(symbol) {
            self.metadata_documentation(symbol)
        } else {
            self.source_documentation(symbol)
        };
        let mut documentation = xml
            .map(|xml| super::parse_documentation(&xml))
            .unwrap_or_default();
        documentation.signature = super::describe_symbol(&self.compilation, symbol);
        documentation.container = container;
        documentation
    }
}

impl View<'_> {
    /// Everything the providers offer at `offset`, sorted.
    pub(super) fn complete(&mut self, offset: u32) -> Completions {
        let text = self.root.full_text();
        let site = Site::new(&self.root, &text, offset);
        let mut items = Vec::new();
        let mut suggestion_mode = false;
        match context::classify(&self.root, &site) {
            Spot::Nothing => {}
            Spot::Documentation => documentation::complete(self, &text, &site, &mut items),
            Spot::Directive => {
                let defined = self.semantic.project.symbols.clone();
                directives::complete(&text, &site, &defined, &mut items);
            }
            Spot::Member(dot) => self.complete_member(&site, &dot, &mut items),
            Spot::UsingMember { path, with_types } => {
                self.using_members(&path, with_types, &mut items);
            }
            Spot::Using { is_static, alias } => {
                symbols::using_items(self, is_static || alias, &mut items);
                if !is_static && !alias {
                    items.push(Completion::keyword("static"));
                }
            }
            Spot::Attribute => {
                symbols::attribute_items(self, &site, &mut items);
            }
            Spot::Override { first } => {
                overrides::complete(self, &text, &site, &first, &mut items);
            }
            Spot::Partial { first } => {
                overrides::complete_partial(self, &text, &site, &first, &mut items);
                for word in ["void", "class", "struct", "interface", "record"] {
                    items.push(Completion::keyword(word));
                }
            }
            Spot::Initializer(initializer) => {
                initializers::complete(self, &site, &initializer, &mut items);
            }
            Spot::Name { ty, of } => {
                if names::complete(self, &ty, of, &mut items) {
                    suggestion_mode = true;
                } else if let Some(target) = site.target.clone() {
                    // Not a type after all: `x |` after a value.
                    let code = context::code_at(&self.root, &target);
                    self.complete_code(&site, &code, &text, &mut items);
                }
            }
            Spot::Code(code) => {
                let code = self.type_arguments(&site, code);
                self.complete_code(&site, &code, &text, &mut items);
            }
        }
        finish(&mut items);
        Completions {
            items,
            start: site.start,
            suggestion_mode,
        }
    }

    /// `List<|` reads as a comparison until the binder says `List` is
    /// generic: then it is where a type argument goes.
    fn type_arguments(&mut self, site: &Site, code: Code) -> Code {
        let Some(target) = &site.target else {
            return code;
        };
        let parent = target.parent().clone();
        if target.kind() != SyntaxKind::LessThanToken
            || parent.kind() != SyntaxKind::LessThanExpression
        {
            return code;
        }
        let Some(left) = parent.children().next() else {
            return code;
        };
        let name = match left.kind() {
            SyntaxKind::ObjectCreationExpression => {
                left.children().find(|child| child.kind().is_type_node())
            }
            SyntaxKind::IdentifierName | SyntaxKind::QualifiedName => Some(left),
            _ => None,
        };
        let Some(name) = name else {
            return code;
        };
        let symbols = self.compilation().symbols();
        let is_generic = |symbol: SymbolId| {
            symbols
                .get(symbol)
                .as_named_type()
                .is_some_and(|ty| ty.arity > 0)
        };
        // `List` alone does not bind — it takes a type argument — so look
        // for a generic type of that name where the code can see.
        let spelled = name
            .text()
            .trim()
            .rsplit('.')
            .next()
            .unwrap_or_default()
            .to_string();
        let mut places = self.namespaces_in_scope(&name);
        places.push(self.compilation().global_namespace());
        places.extend(self.enclosing_types(&name));
        let generic = self.named(&name).is_some_and(is_generic)
            || places.into_iter().any(|place| {
                symbols
                    .lookup(place, &spelled)
                    .iter()
                    .any(|&found| is_generic(found))
            });
        if !generic {
            return code;
        }
        Code {
            type_only: true,
            ..Code::default()
        }
    }

    /// Plain code: keywords, what is in scope, and what the position adds.
    fn complete_code(&mut self, site: &Site, code: &Code, text: &str, items: &mut Vec<Completion>) {
        let around = keywords::Surroundings::of(site.target.as_ref());
        for word in keywords::keywords(code, &around) {
            items.push(Completion::keyword(word));
        }

        let values = code.statement || code.expression;
        let types =
            values || code.type_only || code.member || code.type_declaration || code.constraint;
        if types {
            let from = items.len();
            self.scope_completions(site.start, items);
            let pushed = &mut items[from..];
            let mut kept: Vec<Completion> = pushed.to_vec();
            if values {
                if around.is_static {
                    kept.retain(|item| !symbols::is_instance_member(self, item));
                }
            } else {
                kept.retain(|item| symbols::is_type_like(item.kind));
                if code.base_list {
                    kept.retain(|item| {
                        matches!(
                            item.kind,
                            CompletionKind::Class
                                | CompletionKind::Interface
                                | CompletionKind::Namespace
                        )
                    });
                }
            }
            items.truncate(from);
            items.extend(kept);
            imports::complete_types(self, site, text, !values, items);
        }

        if code.expression || code.after_new || code.pattern {
            symbols::target_typed(self, site, code, items);
        }
        if code.argument
            && let Some(target) = &site.target
        {
            arguments::complete(self, target, items);
        }
        snippets::complete(code, text, site, items);
    }

    /// After a `.`: the members of what is to its left, narrowed to types
    /// where only a type can go, and the extension methods of namespaces the
    /// file does not import.
    fn complete_member(
        &mut self,
        site: &Site,
        dot: &rustlyn_syntax::SyntaxToken,
        items: &mut Vec<Completion>,
    ) {
        self.member_completions(dot, items);
        let parent = dot.parent().clone();
        // How far up the dotted name goes.
        let mut name = parent.clone();
        while let Some(up) = name.parent() {
            if up.kind() == SyntaxKind::QualifiedName {
                name = up.clone();
            } else {
                break;
            }
        }
        let using = name
            .parent()
            .filter(|using| using.kind() == SyntaxKind::UsingDirective)
            .cloned();
        if let Some(using) = using {
            let is_static = using
                .child_token_of_kind(SyntaxKind::StaticKeyword)
                .is_some()
                || using.child_of_kind(SyntaxKind::NameEquals).is_some();
            let left = parent
                .children()
                .next()
                .map(|left| left.text())
                .unwrap_or_default();
            items.clear();
            self.using_members(&left, is_static, items);
            return;
        }
        // `p.Ag other = 1;` is a declaration to the parser, and `p.Ag` the
        // name of a type, but a `p` in scope says what was meant.
        let of_a_value = parent.kind() == SyntaxKind::QualifiedName
            && parent.children().next().is_some_and(|left| {
                !self.named(&left).is_some_and(|symbol| {
                    matches!(
                        self.compilation().symbols().get(symbol).kind,
                        SymbolKind::Namespace | SymbolKind::NamedType
                    )
                }) && self.value_named(&left, dot.span().start()).is_some()
            });
        // `case ActionOnStop.` before the next line's statement reads as a
        // pattern of type `ActionOnStop.Next…`, and in a pattern the name is
        // as likely a constant: the enum's members are what was meant.
        let in_pattern = name.parent().is_some_and(|pattern| {
            matches!(
                pattern.kind(),
                SyntaxKind::RecursivePattern
                    | SyntaxKind::TypePattern
                    | SyntaxKind::DeclarationPattern
                    | SyntaxKind::ConstantPattern
            )
        });
        let type_only = !of_a_value
            && !in_pattern
            && (parent.kind() == SyntaxKind::QualifiedName
                || name.first_token().is_some_and(|first| {
                    context::previous_token(&self.root, &first).is_some_and(|before| {
                        before.kind() == SyntaxKind::NewKeyword
                            || context::code_at(&self.root, &before).type_only
                    })
                }));
        if type_only {
            items.retain(|item| symbols::is_type_like(item.kind));
            return;
        }
        if matches!(
            parent.kind(),
            SyntaxKind::SimpleMemberAccessExpression | SyntaxKind::MemberBindingExpression
        ) {
            imports::complete_extensions(self, site, dot, items);
        }
    }
}

impl View<'_> {
    /// After `using A.B.`: what `A.B` holds — its namespaces, and its types
    /// too after `using static` or `using X =`. A `using` is not bound like
    /// code, so the name is followed by its spelling from the global
    /// namespace down.
    fn using_members(&mut self, path: &str, with_types: bool, items: &mut Vec<Completion>) {
        let symbols = self.compilation().symbols();
        let mut current = Some(self.compilation().global_namespace());
        let path = path.trim().trim_start_matches("global::");
        for part in path
            .split('.')
            .map(str::trim)
            .filter(|part| !part.is_empty())
        {
            current = current.and_then(|container| {
                symbols.lookup_namespace(container, part).or_else(|| {
                    symbols
                        .lookup(container, part)
                        .iter()
                        .copied()
                        .find(|&found| symbols.get(found).kind == SymbolKind::NamedType)
                })
            });
        }
        let Some(container) = current else {
            return;
        };
        for &member in &symbols.get(container).members {
            let kind = symbols.get(member).kind;
            let wanted = kind == SymbolKind::Namespace
                || (with_types && kind == SymbolKind::NamedType && self.offerable(member));
            if wanted {
                self.push_symbol(member, 20, items);
            }
        }
    }
}

/// One line per name and kind, keywords escaped where they are names, and
/// sorted: by rank, then by name.
fn finish(items: &mut Vec<Completion>) {
    let mut seen = HashSet::new();
    items.retain(|item| {
        let edits: Vec<&str> = item
            .additional_edits
            .iter()
            .map(|edit| edit.text.as_str())
            .collect();
        seen.insert((item.label.clone(), item.kind, edits.join("")))
    });
    for item in items.iter_mut() {
        if !matches!(item.kind, CompletionKind::Keyword | CompletionKind::Snippet)
            && item.insert_text.is_none()
            && rustlyn_syntax::kind_from_text(&item.label)
                .is_some_and(SyntaxKind::is_reserved_keyword)
        {
            item.insert_text = Some(format!("@{}", item.label));
        }
    }
    items.sort_by(|a, b| {
        a.rank
            .cmp(&b.rank)
            .then_with(|| a.label.to_lowercase().cmp(&b.label.to_lowercase()))
            .then_with(|| a.label.cmp(&b.label))
    });
}

/// The whitespace at the start of the line `offset` is on.
fn indentation_at(text: &str, offset: u32) -> &str {
    let offset = (offset as usize).min(text.len());
    let line_start = text[..offset].rfind('\n').map_or(0, |at| at + 1);
    let line = &text[line_start..];
    let end = line
        .find(|c: char| c != ' ' && c != '\t')
        .unwrap_or(line.len());
    &line[..end]
}

/// The line break the file uses.
fn newline_of(text: &str) -> &'static str {
    if text.contains("\r\n") { "\r\n" } else { "\n" }
}

/// Whether `word` could be the start of `name`: the same first letter, and
/// every letter of the word in the name in order, ignoring case. How the
/// long lists — unimported types — are cut down before an editor sees them.
fn matches_word(word: &str, name: &str) -> bool {
    let mut letters = name.chars().flat_map(char::to_lowercase);
    let mut wanted = word.chars().flat_map(char::to_lowercase);
    let Some(first) = wanted.next() else {
        return true;
    };
    if letters.next() != Some(first) {
        return false;
    }
    wanted.all(|c| letters.any(|l| l == c))
}

#[cfg(test)]
mod tests;
