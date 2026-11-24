//! `[OverloadResolutionPriority(n)]` (C# 13): among the applicable members a
//! type declares, only those of the highest priority stay candidates.

use std::collections::HashMap;

use rustlyn_syntax::{SyntaxKind, SyntaxNode, TokenValue};

use crate::compilation::Compilation;
use crate::symbol::SymbolId;

/// The priority a member's `[OverloadResolutionPriority]` gives it: 0
/// without one.
pub(crate) fn priority(compilation: &Compilation, member: SymbolId) -> i32 {
    if let Some(priority) = compilation.loaded.priorities.get(&member) {
        return *priority;
    }
    compilation
        .priorities
        .get_or_init(|| declared_priorities(compilation))
        .get(&member)
        .copied()
        .unwrap_or(0)
}

/// Every declaration in the source with a priority on it. A file that never
/// says `OverloadResolutionPriority` is neither parsed nor walked: the text
/// is asked before the tree, as in `obsolete`.
fn declared_priorities(compilation: &Compilation) -> HashMap<SymbolId, i32> {
    let mut found = HashMap::new();
    for tree in compilation.corlib_trees..compilation.trees().len() {
        if !crate::obsolete::says(compilation, tree, "OverloadResolutionPriority") {
            continue;
        }
        let Some(syntax) = compilation.trees().get(tree) else {
            continue;
        };
        for list in syntax
            .root()
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::AttributeList)
        {
            let Some(declaration) = list.parent() else {
                continue;
            };
            let Some(priority) = priority_of(declaration) else {
                continue;
            };
            if let Some(symbol) = compilation.declared_symbol(tree, declaration.span()) {
                found.insert(symbol, priority);
            }
        }
    }
    found
}

fn priority_of(node: &SyntaxNode) -> Option<i32> {
    let attribute = node
        .children()
        .filter(|child| child.kind() == SyntaxKind::AttributeList)
        // `[return: ...]` is not about the member.
        .filter(|list| {
            list.child_of_kind(SyntaxKind::AttributeTargetSpecifier)
                .is_none()
        })
        .flat_map(|list| list.children())
        .filter(|child| child.kind() == SyntaxKind::Attribute)
        .find(|attribute| {
            attribute
                .children()
                .find(|child| child.kind().is_type_node())
                .is_some_and(|name| {
                    let name = name.text();
                    let last = name.trim().rsplit(['.', ':']).next().unwrap_or_default();
                    matches!(
                        last,
                        "OverloadResolutionPriority" | "OverloadResolutionPriorityAttribute"
                    )
                })
        })?;
    let value = attribute
        .child_of_kind(SyntaxKind::AttributeArgumentList)?
        .children()
        .find(|child| child.kind() == SyntaxKind::AttributeArgument)?
        .children()
        .last()?;
    integer(&value)
}

/// An `int` written as a literal, negated or parenthesized.
fn integer(node: &SyntaxNode) -> Option<i32> {
    match node.kind() {
        SyntaxKind::NumericLiteralExpression => match node.first_token()?.value() {
            TokenValue::Int32(value) => Some(*value),
            TokenValue::UInt32(value) => i32::try_from(*value).ok(),
            TokenValue::Int64(value) => i32::try_from(*value).ok(),
            _ => None,
        },
        SyntaxKind::UnaryMinusExpression => integer(&node.children().last()?).map(|v| -v),
        SyntaxKind::ParenthesizedExpression => integer(&node.children().next()?),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use rustlyn_syntax::parse;
    use rustlyn_text::SourceText;

    use super::*;

    #[test]
    fn only_a_file_that_names_the_attribute_is_parsed_to_find_priorities() {
        let compilation = Compilation::create(vec![
            parse(SourceText::new(
                "Ranked.cs",
                "public class Ranked { [OverloadResolutionPriority(2)] public void M() { } }",
            )),
            parse(SourceText::new(
                "Plain.cs",
                "public class Plain { public void N() { } }",
            )),
        ]);
        let read =
            Compilation::read_snapshot(&compilation.write_snapshot()).expect("it reads back");
        let (ranked, plain) = (read.corlib_trees, read.corlib_trees + 1);

        let class = read.type_by_metadata_name("Ranked").expect("Ranked");
        let method = read.symbols().lookup(class, "M")[0];
        assert_eq!(priority(&read, method), 2);
        assert!(read.trees().is_parsed(ranked));
        assert!(
            !read.trees().is_parsed(plain),
            "a file without the attribute stays unparsed"
        );
    }
}
