//! Constant values of enum members, where one is written in terms of another.
//!
//! These once recursed without end — binding a member's initializer folds
//! the members it names, and valuing a member walked every member before
//! it — and took the editor down with them, on a flags enum as ordinary as
//! `All = A | B` written ahead of `A` and `B`.

use rustlyn_semantics::{Binder, Compilation, SymbolId};
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

fn compile(source: &str) -> Compilation {
    Compilation::create(vec![parse(SourceText::new("File0.cs", source))])
}

fn find(compilation: &Compilation, path: &str) -> SymbolId {
    compilation
        .symbols()
        .iter()
        .find(|symbol| compilation.symbols().qualified_name(symbol.id) == path)
        .unwrap_or_else(|| panic!("no symbol named {path}"))
        .id
}

/// The value of the constant at `path`, as the debugger would print it.
fn value(compilation: &Compilation, path: &str) -> Option<String> {
    Binder::new(compilation)
        .constant_value(find(compilation, path))
        .map(|value| format!("{value:?}"))
}

#[test]
fn a_member_written_ahead_of_the_members_it_names_has_their_value() {
    let compilation = compile("enum Flags { All = A | B, A = 1, B = 2, C }");
    // Each asked first, in its own compilation: the cache must not be what
    // makes the answer come out.
    for (path, digit) in [
        ("Flags.A", "1"),
        ("Flags.B", "2"),
        ("Flags.All", "3"),
        ("Flags.C", "3"),
    ] {
        let compilation = compile("enum Flags { All = A | B, A = 1, B = 2, C }");
        let found = value(&compilation, path).unwrap_or_else(|| panic!("{path} has no value"));
        assert!(found.contains(digit), "{path} is {found}, not {digit}");
    }
    assert!(value(&compilation, "Flags.All").is_some());
}

#[test]
fn members_defined_in_terms_of_each_other_have_no_value_rather_than_no_end() {
    let compilation = compile("enum Loop { A = B, B = A, C }");
    assert_eq!(value(&compilation, "Loop.A"), None);
    assert_eq!(value(&compilation, "Loop.B"), None);
    let compilation = compile("enum Self { A = A + 1 }");
    assert_eq!(value(&compilation, "Self.A"), None);
}
