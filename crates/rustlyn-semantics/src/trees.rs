//! The syntax trees of a compilation, parsed when first asked for.
//!
//! A compilation built from source has every tree in hand: declaring the
//! program meant parsing all of it. A compilation read back from disk does
//! not, and should not have to — the declarations are already in its symbol
//! table, and a tree is needed only when something asks about the syntax of
//! one file: a body to bind, a type written in a signature to resolve. Most
//! files of a large project are never asked about in a session, so a tree is
//! kept as its text until it is, and parsed on the spot the first time.
//!
//! Parsing is deterministic, so the tree made later is the tree the
//! declarations were made from: the same text under the same options gives
//! the same spans.

use std::sync::{Arc, OnceLock};

use rustlyn_syntax::{ParseOptions, SyntaxTree, parse_with};
use rustlyn_text::SourceText;

/// One file: its tree, or what it takes to make one.
#[derive(Debug)]
struct Slot {
    tree: OnceLock<SyntaxTree>,
    source: SourceText,
    options: Arc<ParseOptions>,
}

/// The trees of a compilation, in the order the compilation numbers them.
#[derive(Debug, Default)]
pub struct Trees {
    slots: Vec<Slot>,
}

impl Trees {
    /// Trees parsed already.
    #[must_use]
    pub fn parsed(trees: Vec<SyntaxTree>) -> Self {
        Self {
            slots: trees
                .into_iter()
                .map(|tree| Slot {
                    source: tree.source().clone(),
                    // A tree remembers the symbols it was parsed under, which
                    // is all its options are.
                    options: Arc::new(ParseOptions::with_symbols(tree.defined().iter().cloned())),
                    tree: OnceLock::from(tree),
                })
                .collect(),
        }
    }

    /// The preprocessor symbols file `index` is parsed under.
    #[must_use]
    pub fn defined(&self, index: usize) -> &[String] {
        self.slots
            .get(index)
            .map_or(&[], |slot| slot.options.preprocessor_symbols.as_slice())
    }

    /// Files not parsed yet, each with the options it is to be parsed under.
    #[must_use]
    pub fn unparsed(sources: Vec<(SourceText, Arc<ParseOptions>)>) -> Self {
        Self {
            slots: sources
                .into_iter()
                .map(|(source, options)| Slot {
                    tree: OnceLock::new(),
                    source,
                    options,
                })
                .collect(),
        }
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.slots.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }

    /// Tree `index`, parsed now if it has not been.
    #[must_use]
    pub fn get(&self, index: usize) -> Option<&SyntaxTree> {
        let slot = self.slots.get(index)?;
        Some(
            slot.tree
                .get_or_init(|| parse_with(slot.source.clone(), &slot.options)),
        )
    }

    /// The text of file `index`, without parsing it.
    #[must_use]
    pub fn source(&self, index: usize) -> Option<&SourceText> {
        self.slots.get(index).map(|slot| &slot.source)
    }

    /// Whether tree `index` has been parsed.
    #[must_use]
    pub fn is_parsed(&self, index: usize) -> bool {
        self.slots
            .get(index)
            .is_some_and(|slot| slot.tree.get().is_some())
    }

    /// The same trees with file `index` given by `tree`: the others are
    /// shared, parsed or not as they were.
    #[must_use]
    pub fn with_replaced(&self, index: usize, tree: SyntaxTree) -> Self {
        let slots = self
            .slots
            .iter()
            .enumerate()
            .map(|(at, slot)| {
                if at == index {
                    Slot {
                        source: tree.source().clone(),
                        options: Arc::new(ParseOptions::with_symbols(
                            tree.defined().iter().cloned(),
                        )),
                        tree: OnceLock::from(tree.clone()),
                    }
                } else {
                    let kept = OnceLock::new();
                    if let Some(parsed) = slot.tree.get() {
                        let _ = kept.set(parsed.clone());
                    }
                    Slot {
                        tree: kept,
                        source: slot.source.clone(),
                        options: slot.options.clone(),
                    }
                }
            })
            .collect();
        Self { slots }
    }

    /// Every tree, parsing each that has not been.
    pub fn iter(&self) -> impl Iterator<Item = &SyntaxTree> {
        (0..self.len()).filter_map(|index| self.get(index))
    }
}

impl std::ops::Index<usize> for Trees {
    type Output = SyntaxTree;

    fn index(&self, index: usize) -> &SyntaxTree {
        self.get(index).expect("a tree of this compilation")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_unparsed_tree_is_parsed_once_and_the_same_as_parsing_it_then() {
        let text = "#if FAST\nclass A { }\n#else\nclass B { }\n#endif\n";
        let options = Arc::new(ParseOptions::with_symbols(["FAST"]));
        let trees = Trees::unparsed(vec![(SourceText::new("A.cs", text), options.clone())]);
        assert!(!trees.is_parsed(0));
        assert_eq!(trees.source(0).map(SourceText::text), Some(text));
        assert!(!trees.is_parsed(0), "reading the text parses nothing");
        let tree = &trees[0];
        assert!(trees.is_parsed(0));
        let direct = parse_with(SourceText::new("A.cs", text), &options);
        assert_eq!(tree.root().debug_tree(), direct.root().debug_tree());
        assert!(std::ptr::eq(tree, &trees[0]), "and parsed once");
    }
}
