//! Names for something being declared, from its type: after `int |` Roslyn's
//! `DeclarationNameCompletionProvider` offers `count` and `index`, after
//! `StringBuilder |` it offers `stringBuilder` and `builder`, after
//! `List<Item> |` it offers `items`. The list is in suggestion mode: the name
//! is new, so none of these is the only right answer, and a space must not
//! commit one.

use rustlyn_semantics::{SpecialType, SymbolId, Type, TypeKind};
use rustlyn_syntax::{SyntaxKind as K, SyntaxNode};

use super::context::NameOf;
use super::{Completion, CompletionKind, View};

/// Offers names after the type `ty`. False when `ty` is not a type after
/// all, and the place is plain code.
pub(super) fn complete(
    view: &mut View<'_>,
    ty: &SyntaxNode,
    of: NameOf,
    items: &mut Vec<Completion>,
) -> bool {
    if ty.kind() == K::Parameter {
        // The type is the lone word the parser took for a name.
        let Some(word) = ty.child_token_of_kind(K::IdentifierToken) else {
            return false;
        };
        let spelled = word.value_text().to_string();
        let found = type_named(view, ty, &spelled);
        let words = match found {
            Some(symbol) => suggestions(view, &Type::named(symbol)),
            None => words_for_name(&spelled, false),
        };
        push_names(&words, of, items);
        return true;
    }
    let declared = if ty.kind() == K::IdentifierName
        && ty.parent().is_some_and(|parent| {
            matches!(parent.kind(), K::ExpressionStatement | K::GlobalStatement)
        }) {
        // `Foo |` alone: a declaration only when `Foo` names a type.
        let Some(symbol) = view.named(ty) else {
            return false;
        };
        if view.compilation().symbols().get(symbol).kind != rustlyn_semantics::SymbolKind::NamedType
        {
            return false;
        }
        view.model.type_of_syntax(ty)
    } else {
        view.model.type_of_syntax(ty)
    };
    if matches!(declared, Type::Error) && ty.kind() != K::PredefinedType {
        // Unknown, but written where a type goes: name it by its spelling.
        let spelled = ty.text().trim().to_string();
        push_names(&words_for_name(&spelled, false), of, items);
        return true;
    }
    let words = suggestions(view, &declared);
    push_names(&words, of, items);
    true
}

/// A type called `name` that the code at `node` can see.
fn type_named(view: &View<'_>, node: &SyntaxNode, name: &str) -> Option<SymbolId> {
    let symbols = view.compilation().symbols();
    let mut places = view.namespaces_in_scope(node);
    places.push(view.compilation().global_namespace());
    places.extend(view.enclosing_types(node));
    places.into_iter().find_map(|place| {
        symbols
            .lookup(place, name)
            .iter()
            .copied()
            .find(|&found| symbols.get(found).kind == rustlyn_semantics::SymbolKind::NamedType)
    })
}

fn push_names(words: &[Vec<String>], of: NameOf, items: &mut Vec<Completion>) {
    let kind = match of {
        NameOf::Local => CompletionKind::Local,
        NameOf::Parameter => CompletionKind::Parameter,
        NameOf::Member { public: true } => CompletionKind::Property,
        NameOf::Member { public: false } => CompletionKind::Field,
    };
    let pascal = matches!(of, NameOf::Member { public: true });
    for (rank, parts) in words.iter().enumerate() {
        let name = join(parts, pascal);
        if name.is_empty() || items.iter().any(|item| item.label == name) {
            continue;
        }
        items.push(Completion {
            label: name,
            kind,
            rank: u8::try_from(rank).unwrap_or(u8::MAX),
            ..Completion::default()
        });
    }
}

/// Parts of a name, joined in camel or Pascal case.
fn join(parts: &[String], pascal: bool) -> String {
    let mut name = String::new();
    for (index, part) in parts.iter().enumerate() {
        let mut chars = part.chars();
        let Some(first) = chars.next() else {
            continue;
        };
        if index == 0 && !pascal {
            name.extend(first.to_lowercase());
        } else {
            name.extend(first.to_uppercase());
        }
        name.push_str(chars.as_str());
    }
    name
}

/// Names for a value of `ty`, each as its words, best first.
fn suggestions(view: &View<'_>, ty: &Type) -> Vec<Vec<String>> {
    let symbols = view.compilation().symbols();
    match ty {
        Type::Array { element, .. } => plural(&suggestions(view, element)),
        Type::Named {
            symbol,
            type_arguments,
        } => {
            if let Some(special) = special_type(view, *symbol) {
                return predefined(special);
            }
            if let Some(element) = collection_element(view, *symbol, type_arguments) {
                let mut names = plural(&suggestions(view, &element));
                names.extend(words_for_name(&symbols.get(*symbol).name, true));
                return names;
            }
            if symbols.qualified_name(*symbol) == "System.Nullable`1"
                && let Some(inner) = type_arguments.first()
            {
                return suggestions(view, inner);
            }
            let found = symbols.get(*symbol);
            let is_interface = found.type_kind() == Some(TypeKind::Interface);
            words_for_name(&found.name, is_interface)
        }
        Type::TypeParameter(symbol) => {
            let name = &symbols.get(*symbol).name;
            // `T` alone says nothing; `TItem` says `item`.
            let stem = name
                .strip_prefix('T')
                .filter(|rest| rest.starts_with(|c: char| c.is_ascii_uppercase()));
            match stem {
                Some(stem) => words_for_name(stem, false),
                None => vec![vec!["value".to_string()]],
            }
        }
        Type::Tuple(_) => vec![vec!["tuple".to_string()]],
        _ => Vec::new(),
    }
}

fn special_type(view: &View<'_>, symbol: SymbolId) -> Option<SpecialType> {
    SpecialType::ALL
        .iter()
        .copied()
        .find(|&special| view.compilation().special_type(special) == Some(symbol))
}

/// Names for the built-in types, which say nothing by their own names.
fn predefined(special: SpecialType) -> Vec<Vec<String>> {
    let words: &[&str] = match special.keyword() {
        "int" | "long" | "short" | "uint" | "ulong" | "ushort" | "nint" | "nuint" => {
            &["count", "index", "value", "number"]
        }
        "byte" | "sbyte" => &["value", "b"],
        "bool" => &["flag", "enabled", "value"],
        "string" => &["text", "name", "value", "s"],
        "char" => &["c", "character"],
        "double" | "float" | "decimal" => &["value", "amount"],
        "object" => &["obj", "value"],
        _ => &["value"],
    };
    words.iter().map(|word| vec![(*word).to_string()]).collect()
}

/// The element type of a generic collection: `T` of `List<T>`,
/// `IEnumerable<T>` and whatever implements it.
fn collection_element(view: &View<'_>, symbol: SymbolId, arguments: &[Type]) -> Option<Type> {
    if arguments.len() != 1 {
        return None;
    }
    let symbols = view.compilation().symbols();
    let name = symbols.qualified_name(symbol);
    let enumerable = "System.Collections.Generic.IEnumerable`1";
    if name == enumerable
        || view
            .types_of(&Type::Named {
                symbol,
                type_arguments: arguments.to_vec(),
            })
            .into_iter()
            .any(|base| symbols.qualified_name(base) == enumerable)
    {
        return arguments.first().cloned();
    }
    None
}

/// Each name with its last word made plural.
fn plural(names: &[Vec<String>]) -> Vec<Vec<String>> {
    names
        .iter()
        .map(|parts| {
            let mut parts = parts.clone();
            if let Some(last) = parts.last_mut() {
                *last = pluralize(last);
            }
            parts
        })
        .collect()
}

fn pluralize(word: &str) -> String {
    let lower = word.to_ascii_lowercase();
    if lower.ends_with('s')
        || lower.ends_with('x')
        || lower.ends_with("ch")
        || lower.ends_with("sh")
    {
        format!("{word}es")
    } else if lower.ends_with('y')
        && !matches!(
            lower.chars().rev().nth(1),
            Some('a' | 'e' | 'i' | 'o' | 'u')
        )
    {
        format!("{}ies", &word[..word.len() - 1])
    } else {
        format!("{word}s")
    }
}

/// Names from a type's own name: every tail of its words, longest first.
/// `StringBuilder` gives `stringBuilder` and `builder`; an interface's `I`
/// is dropped.
fn words_for_name(name: &str, is_interface: bool) -> Vec<Vec<String>> {
    let name = name.split('<').next().unwrap_or(name);
    let name = name.rsplit('.').next().unwrap_or(name);
    let name = if is_interface
        && name.len() > 1
        && name.starts_with('I')
        && name[1..].starts_with(|c: char| c.is_ascii_uppercase())
    {
        &name[1..]
    } else {
        name
    };
    let words = split_words(name);
    (0..words.len())
        .map(|from| words[from..].to_vec())
        .collect()
}

/// `HTTPServerName` → `HTTP`, `Server`, `Name`; `stringBuilder` → `string`,
/// `Builder`.
fn split_words(name: &str) -> Vec<String> {
    let chars: Vec<char> = name.chars().filter(|c| *c != '_').collect();
    let mut words = Vec::new();
    let mut current = String::new();
    for (index, &c) in chars.iter().enumerate() {
        let starts_word = c.is_uppercase()
            && index > 0
            && (chars[index - 1].is_lowercase()
                || chars[index - 1].is_ascii_digit()
                || chars.get(index + 1).is_some_and(|next| next.is_lowercase()));
        if starts_word && !current.is_empty() {
            words.push(std::mem::take(&mut current));
        }
        current.push(c);
    }
    if !current.is_empty() {
        words.push(current);
    }
    // An all-capitals word reads as a word, not letters: `HTTP` → `Http`.
    words
        .into_iter()
        .map(|word| {
            if word.len() > 1 && word.chars().all(|c| !c.is_lowercase()) {
                let mut chars = word.chars();
                let first = chars.next().unwrap_or_default();
                format!("{first}{}", chars.as_str().to_lowercase())
            } else {
                word
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn words_split_at_humps() {
        assert_eq!(split_words("StringBuilder"), vec!["String", "Builder"]);
        assert_eq!(split_words("HTTPServer"), vec!["Http", "Server"]);
        assert_eq!(
            words_for_name("IEnumerable", true),
            vec![vec!["Enumerable".to_string()]]
        );
        assert_eq!(
            join(&["String".into(), "Builder".into()], false),
            "stringBuilder"
        );
        assert_eq!(pluralize("Item"), "Items");
        assert_eq!(pluralize("Entry"), "Entries");
        assert_eq!(pluralize("Box"), "Boxes");
    }
}
