//! The project's declarations by name, for what the compiler does not
//! answer: a field guessed by its name when the compiler did not know it,
//! the implementations of a member when the compiler found none, the
//! members of base types, the fields of a type in a linked project.
//!
//! [`IndexSymbols`] reads them from the session's project index. A host
//! with an index of its own (one that also holds declarations a source
//! generator will add) implements [`Symbols`] over that.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use rustlyn_ide::index::ProjectIndex;
use rustlyn_ide::outline::DeclarationKind;

use super::text::join;

/// What a symbol is, as far as the value graph cares.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolKind {
    Type,
    Method,
    Field,
    Property,
    Other,
}

/// One declaration of the project.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Symbol {
    pub name: String,
    pub kind: SymbolKind,
    /// The type (or namespace) that holds it, as the index names it; the
    /// value graph compares its last part.
    pub container: Option<String>,
    /// A field's or property's type, as written.
    pub type_text: Option<String>,
    /// A type's bases, as written.
    pub bases: Vec<String>,
    /// How many parameters a method has.
    pub parameters: usize,
    /// Absolute.
    pub path: String,
    pub line: usize,
    /// UTF-16 code units from the start of the line.
    pub character: usize,
    /// The name's length, UTF-16.
    pub length: usize,
}

impl Symbol {
    /// `Container.Name`, or the name alone.
    #[must_use]
    pub fn qualified(&self) -> String {
        match &self.container {
            Some(container) => format!("{container}.{}", self.name),
            None => self.name.clone(),
        }
    }

    /// Whether it holds a value: a field or a property.
    #[must_use]
    pub fn is_value(&self) -> bool {
        matches!(self.kind, SymbolKind::Field | SymbolKind::Property)
    }
}

/// The project's declarations by name.
pub trait Symbols: Send + Sync {
    /// Every declaration with this plain name.
    fn named(&self, name: &str) -> Vec<Symbol>;
    /// The types with this plain name.
    fn types_named(&self, name: &str) -> Vec<Symbol>;
    /// The members of the types with this plain name.
    fn members_of(&self, owner: &str) -> Vec<Symbol>;
    /// The types that name this one (its plain name, [`base_key`]) among
    /// their bases.
    fn derived_from(&self, base: &str) -> Vec<Symbol>;
    /// Every field and property of the project.
    fn values(&self) -> Vec<Symbol>;
    /// The fields of an ECS stash type (`Stash<Health>`) of this component
    /// — declared ones, and those a source generator adds when the host
    /// knows them. By default, the declared fields whose type says so.
    fn stashes(&self, component: &str) -> Vec<Symbol> {
        self.values()
            .into_iter()
            .filter(|s| {
                s.kind == SymbolKind::Field
                    && s.type_text.as_deref().and_then(super::ecs::stash_component)
                        == Some(component.to_owned())
            })
            .collect()
    }
}

/// The key of a base: the name without namespace and generic arguments.
/// `Game.Ecs.Base<T>` → `Base`.
#[must_use]
pub fn base_key(text: &str) -> String {
    let mut name = text.trim();
    if let Some(lt) = name.find('<') {
        name = &name[..lt];
    }
    if let Some(dot) = name.rfind('.') {
        name = &name[dot + 1..];
    }
    name.to_owned()
}

/// The last part of a dotted name.
fn last_part(name: &str) -> &str {
    name.rsplit('.').find(|p| !p.is_empty()).unwrap_or(name)
}

const fn symbol_kind(kind: DeclarationKind) -> SymbolKind {
    match kind {
        DeclarationKind::Class
        | DeclarationKind::Struct
        | DeclarationKind::Interface
        | DeclarationKind::Enum
        | DeclarationKind::Record
        | DeclarationKind::Delegate => SymbolKind::Type,
        DeclarationKind::Method => SymbolKind::Method,
        DeclarationKind::Field => SymbolKind::Field,
        DeclarationKind::Property | DeclarationKind::Indexer => SymbolKind::Property,
        _ => SymbolKind::Other,
    }
}

/// [`Symbols`] over the session's project index.
#[derive(Debug)]
pub struct IndexSymbols {
    index: Arc<ProjectIndex>,
    by_name: HashMap<String, Vec<u32>>,
    types_by_name: HashMap<String, Vec<u32>>,
    members_by_owner: HashMap<String, Vec<u32>>,
    derived_by_base: HashMap<String, Vec<u32>>,
    values: Vec<u32>,
    /// File texts, for the lines and UTF-16 columns of names.
    texts: Mutex<HashMap<PathBuf, Arc<String>>>,
}

impl IndexSymbols {
    #[must_use]
    pub fn new(index: Arc<ProjectIndex>) -> Self {
        let mut symbols = Self {
            index: index.clone(),
            by_name: HashMap::new(),
            types_by_name: HashMap::new(),
            members_by_owner: HashMap::new(),
            derived_by_base: HashMap::new(),
            values: Vec::new(),
            texts: Mutex::new(HashMap::new()),
        };
        for (i, entry) in index.entries().iter().enumerate() {
            let id = u32::try_from(i).unwrap_or(u32::MAX);
            let declaration = &entry.declaration;
            symbols
                .by_name
                .entry(declaration.name.clone())
                .or_default()
                .push(id);
            match symbol_kind(declaration.kind) {
                SymbolKind::Type => {
                    symbols
                        .types_by_name
                        .entry(declaration.name.clone())
                        .or_default()
                        .push(id);
                    for base in &declaration.bases {
                        symbols
                            .derived_by_base
                            .entry(base_key(base))
                            .or_default()
                            .push(id);
                    }
                }
                kind => {
                    if let Some(container) = &declaration.container {
                        symbols
                            .members_by_owner
                            .entry(last_part(container).to_owned())
                            .or_default()
                            .push(id);
                    }
                    if matches!(kind, SymbolKind::Field | SymbolKind::Property) {
                        symbols.values.push(id);
                    }
                }
            }
        }
        symbols
    }

    fn text(&self, path: &Path) -> Option<Arc<String>> {
        let mut texts = self.texts.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(text) = texts.get(path) {
            return Some(text.clone());
        }
        let text = Arc::new(std::fs::read_to_string(path).ok()?);
        texts.insert(path.to_path_buf(), text.clone());
        Some(text)
    }

    fn symbol(&self, id: u32) -> Option<Symbol> {
        let entry = self.index.entry(id)?;
        let file = self.index.file_of(id)?;
        let absolute = self.index.root().join(&file.path);
        let declaration = &entry.declaration;
        let (mut line, mut character, mut length) = (declaration.line as usize, 0, 0);
        if let Some(text) = self.text(&absolute) {
            let mut start = (declaration.name_span.start() as usize).min(text.len());
            while !text.is_char_boundary(start) {
                start -= 1;
            }
            let line_start = text[..start].rfind('\n').map_or(0, |at| at + 1);
            line = text[..start].bytes().filter(|&b| b == b'\n').count();
            character = text[line_start..start].encode_utf16().count();
            length = text
                .get(start..start + declaration.name_span.length() as usize)
                .map_or(0, |name| name.encode_utf16().count());
        }
        let root = self.index.root().to_string_lossy();
        Some(Symbol {
            name: declaration.name.clone(),
            kind: symbol_kind(declaration.kind),
            container: declaration.container.clone().filter(|c| !c.is_empty()),
            type_text: declaration.type_text.clone().filter(|t| !t.is_empty()),
            bases: declaration.bases.clone(),
            parameters: declaration.parameters.len(),
            path: join(&root, &file.path.to_string_lossy()),
            line,
            character,
            length,
        })
    }

    fn all(&self, ids: Option<&Vec<u32>>) -> Vec<Symbol> {
        ids.map(Vec::as_slice)
            .unwrap_or(&[])
            .iter()
            .filter_map(|&id| self.symbol(id))
            .collect()
    }
}

impl Symbols for IndexSymbols {
    fn named(&self, name: &str) -> Vec<Symbol> {
        self.all(self.by_name.get(name))
    }

    fn types_named(&self, name: &str) -> Vec<Symbol> {
        self.all(self.types_by_name.get(name))
    }

    fn members_of(&self, owner: &str) -> Vec<Symbol> {
        self.all(self.members_by_owner.get(owner))
    }

    fn derived_from(&self, base: &str) -> Vec<Symbol> {
        self.all(self.derived_by_base.get(base))
    }

    fn values(&self) -> Vec<Symbol> {
        self.all(Some(&self.values))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn base_keys() {
        assert_eq!(base_key("Game.Ecs.Base<T>"), "Base");
        assert_eq!(base_key(" IFoo "), "IFoo");
    }
}
