//! Naming rules: IDE1006, a name that breaks a rule the `.editorconfig`
//! writes down, and the fix that renames it.
//!
//! A rule is three sets of keys, joined by the names they give each other:
//!
//! ```text
//! dotnet_naming_rule.private_fields.symbols  = private_fields
//! dotnet_naming_rule.private_fields.style    = underscore_camel
//! dotnet_naming_rule.private_fields.severity = warning
//! dotnet_naming_symbols.private_fields.applicable_kinds           = field
//! dotnet_naming_symbols.private_fields.applicable_accessibilities = private
//! dotnet_naming_symbols.private_fields.required_modifiers         = readonly
//! dotnet_naming_style.underscore_camel.required_prefix = _
//! dotnet_naming_style.underscore_camel.capitalization  = camel_case
//! ```
//!
//! Every declaration is matched against the rules, most specific first as
//! Roslyn orders them — an explicit `priority`, then more required
//! modifiers, fewer accessibilities, fewer kinds — and the first rule that
//! applies decides: if the name does not have its style, it is reported,
//! and the fix renames it to the nearest name that does, through the
//! renamer, so every use follows.
//!
//! What a declaration is — its kind, accessibility and modifiers — is read
//! from the syntax, with C#'s defaults where nothing is written. Overrides
//! and explicit interface implementations are left alone: their names are
//! not theirs to choose.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use rustlyn_diagnostics::Severity;
use rustlyn_syntax::{SyntaxKind as K, SyntaxNode, SyntaxToken};
use rustlyn_text::TextSpan;

use super::{ActionKind, AnalyzerDiagnostic, CodeAction, RenameOptions, Semantic, View};
use crate::editorconfig::{Configured, Settings};

/// How a style capitalizes the words of a name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Capitalization {
    PascalCase,
    CamelCase,
    FirstWordUpper,
    AllUpper,
    AllLower,
}

/// A `dotnet_naming_style`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamingStyle {
    pub prefix: String,
    pub suffix: String,
    pub separator: String,
    pub capitalization: Option<Capitalization>,
}

/// A `dotnet_naming_symbols`: what a rule applies to. Empty lists apply to
/// everything, as does `*`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SymbolSpecification {
    pub kinds: Vec<String>,
    pub accessibilities: Vec<String>,
    pub modifiers: Vec<String>,
}

/// A `dotnet_naming_rule`, with what it names resolved.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamingRule {
    pub name: String,
    pub symbols: SymbolSpecification,
    pub style: NamingStyle,
    /// `None` for `none`: the rule applies, and says nothing.
    pub severity: Option<Severity>,
    pub priority: Option<i64>,
}

/// The kinds, accessibilities and modifiers Roslyn lists for "everything".
const ALL_KINDS: usize = 14;
const ALL_ACCESSIBILITIES: usize = 7;

/// The rules the settings write down, in the order they are tried.
#[must_use]
pub fn rules(settings: &Settings) -> Vec<NamingRule> {
    let mut names: Vec<String> = settings
        .iter()
        .filter_map(|(key, _)| {
            key.strip_prefix("dotnet_naming_rule.")
                .and_then(|rest| rest.rsplit_once('.'))
                .filter(|(_, property)| *property == "symbols")
                .map(|(name, _)| name.to_owned())
        })
        .collect();
    names.dedup();
    let list = |key: String| -> Vec<String> {
        settings
            .get(&key)
            .map(|value| {
                value
                    .split(',')
                    .map(|item| item.trim().to_ascii_lowercase())
                    .filter(|item| !item.is_empty())
                    .collect()
            })
            .unwrap_or_default()
    };
    let mut found = Vec::new();
    for name in names {
        let rule = |property: &str| settings.get(&format!("dotnet_naming_rule.{name}.{property}"));
        let (Some(symbols), Some(style)) = (rule("symbols"), rule("style")) else {
            continue;
        };
        let symbols = symbols.trim().to_ascii_lowercase();
        let style = style.trim().to_ascii_lowercase();
        let style_key = |property: &str| format!("dotnet_naming_style.{style}.{property}");
        let capitalization = match settings.value(&style_key("capitalization")).as_deref() {
            Some("pascal_case") => Some(Capitalization::PascalCase),
            Some("camel_case") => Some(Capitalization::CamelCase),
            Some("first_word_upper") => Some(Capitalization::FirstWordUpper),
            Some("all_upper") => Some(Capitalization::AllUpper),
            Some("all_lower") => Some(Capitalization::AllLower),
            _ => None,
        };
        let severity = match rule("severity").map(|value| value.trim().to_ascii_lowercase()) {
            Some(value) if value == "none" => None,
            Some(value) if value == "silent" || value == "refactoring" => Some(Severity::Hidden),
            Some(value) if value == "suggestion" => Some(Severity::Info),
            Some(value) if value == "error" => Some(Severity::Error),
            Some(value) if value == "warning" => Some(Severity::Warning),
            _ => Some(Severity::Hidden),
        };
        found.push(NamingRule {
            symbols: SymbolSpecification {
                kinds: list(format!("dotnet_naming_symbols.{symbols}.applicable_kinds")),
                accessibilities: list(format!(
                    "dotnet_naming_symbols.{symbols}.applicable_accessibilities"
                )),
                modifiers: list(format!(
                    "dotnet_naming_symbols.{symbols}.required_modifiers"
                )),
            },
            style: NamingStyle {
                prefix: settings
                    .get(&style_key("required_prefix"))
                    .unwrap_or("")
                    .to_owned(),
                suffix: settings
                    .get(&style_key("required_suffix"))
                    .unwrap_or("")
                    .to_owned(),
                separator: settings
                    .get(&style_key("word_separator"))
                    .unwrap_or("")
                    .to_owned(),
                capitalization,
            },
            severity,
            priority: rule("priority").and_then(|value| value.trim().parse().ok()),
            name,
        });
    }
    let count = |items: &[String], all: usize| {
        if items.is_empty() || items.iter().any(|item| item == "*") {
            all
        } else {
            items.len()
        }
    };
    found.sort_by(|a, b| {
        a.priority
            .unwrap_or(i64::MAX)
            .cmp(&b.priority.unwrap_or(i64::MAX))
            .then(b.symbols.modifiers.len().cmp(&a.symbols.modifiers.len()))
            .then(
                count(&a.symbols.accessibilities, ALL_ACCESSIBILITIES)
                    .cmp(&count(&b.symbols.accessibilities, ALL_ACCESSIBILITIES)),
            )
            .then(count(&a.symbols.kinds, ALL_KINDS).cmp(&count(&b.symbols.kinds, ALL_KINDS)))
            .then(a.name.cmp(&b.name))
    });
    found
}

/// A declared name and what the rules match it by.
#[derive(Clone, Debug)]
struct Declared {
    token: SyntaxToken,
    kind: &'static str,
    accessibility: &'static str,
    modifiers: Vec<&'static str>,
}

impl SymbolSpecification {
    fn applies_to(&self, declared: &Declared) -> bool {
        let any = |items: &[String], wanted: &str| {
            items.is_empty() || items.iter().any(|item| item == "*" || item == wanted)
        };
        let accessibility = match declared.accessibility {
            "internal" => ["internal", "friend"]
                .iter()
                .any(|alias| any(&self.accessibilities, alias)),
            other => any(&self.accessibilities, other),
        };
        any(&self.kinds, declared.kind)
            && accessibility
            && self.modifiers.iter().all(|modifier| {
                let modifier = match modifier.as_str() {
                    "shared" => "static",
                    "must_inherit" => "abstract",
                    other => other,
                };
                declared.modifiers.contains(&modifier)
                    // A constant is static, as far as naming goes.
                    || (modifier == "static" && declared.modifiers.contains(&"const"))
            })
    }
}

impl NamingStyle {
    /// Whether `name` has this style: its prefix, its suffix, and each word
    /// between capitalized as it says.
    #[must_use]
    pub fn accepts(&self, name: &str) -> bool {
        let Some(middle) = name
            .strip_prefix(self.prefix.as_str())
            .and_then(|rest| rest.strip_suffix(self.suffix.as_str()))
        else {
            return false;
        };
        if middle.is_empty() {
            return false;
        }
        let Some(capitalization) = self.capitalization else {
            return true;
        };
        let words: Vec<&str> = if self.separator.is_empty() {
            vec![middle]
        } else {
            middle.split(self.separator.as_str()).collect()
        };
        let first_upper = |word: &str| word.chars().next().is_some_and(char::is_uppercase);
        let first_lower = |word: &str| word.chars().next().is_some_and(char::is_lowercase);
        match capitalization {
            Capitalization::PascalCase => words.iter().all(|word| first_upper(word)),
            Capitalization::CamelCase => {
                first_lower(words[0]) && words[1..].iter().all(|word| first_upper(word))
            }
            Capitalization::FirstWordUpper => {
                first_upper(words[0])
                    && words[1..]
                        .iter()
                        .all(|word| !word.chars().any(char::is_uppercase))
            }
            Capitalization::AllUpper => !middle.chars().any(char::is_lowercase),
            Capitalization::AllLower => !middle.chars().any(char::is_uppercase),
        }
    }

    /// The name nearest to `name` that has this style: its words, as the
    /// underscores and the humps of its case split it, recapitalized and
    /// joined, between the prefix and the suffix.
    #[must_use]
    pub fn make_compliant(&self, name: &str) -> String {
        let mut middle = name;
        if !self.prefix.is_empty() {
            middle = middle.strip_prefix(self.prefix.as_str()).unwrap_or(middle);
        }
        if !self.suffix.is_empty() {
            middle = middle.strip_suffix(self.suffix.as_str()).unwrap_or(middle);
        }
        // A leftover `_` or `m_`-style marker is not a word.
        let middle = middle.trim_matches('_');
        let middle = ["m_", "s_", "t_"]
            .iter()
            .find_map(|marker| middle.strip_prefix(marker))
            .filter(|rest| !rest.is_empty())
            .unwrap_or(middle);
        let words = split_words(middle, &self.separator);
        let cased: Vec<String> = words
            .iter()
            .enumerate()
            .map(|(index, word)| match self.capitalization {
                Some(Capitalization::PascalCase) => upper_first(word),
                Some(Capitalization::CamelCase) => {
                    if index == 0 {
                        lower_first(word)
                    } else {
                        upper_first(word)
                    }
                }
                Some(Capitalization::FirstWordUpper) => {
                    if index == 0 {
                        upper_first(&word.to_lowercase())
                    } else {
                        word.to_lowercase()
                    }
                }
                Some(Capitalization::AllUpper) => word.to_uppercase(),
                Some(Capitalization::AllLower) => word.to_lowercase(),
                None => (*word).to_owned(),
            })
            .collect();
        let separator = if self.separator.is_empty()
            && self
                .capitalization
                .is_some_and(|c| matches!(c, Capitalization::AllUpper | Capitalization::AllLower))
        {
            // `ALLCAPS` of two words keeps them apart the one way it can.
            "_"
        } else {
            self.separator.as_str()
        };
        let joined = if self.separator.is_empty()
            && !matches!(
                self.capitalization,
                Some(Capitalization::AllUpper | Capitalization::AllLower)
            ) {
            cased.concat()
        } else {
            cased.join(separator)
        };
        format!("{}{joined}{}", self.prefix, self.suffix)
    }
}

/// The words of a name: split at the separator, at underscores, and where
/// a lower-case letter or digit is followed by an upper-case one.
fn split_words<'a>(name: &'a str, separator: &str) -> Vec<&'a str> {
    let mut words = Vec::new();
    let pieces: Vec<&str> = if separator.is_empty() {
        name.split('_').collect()
    } else {
        name.split(separator)
            .flat_map(|piece| piece.split('_'))
            .collect()
    };
    for piece in pieces {
        let mut start = 0;
        let chars: Vec<(usize, char)> = piece.char_indices().collect();
        for window in chars.windows(2) {
            let ((_, before), (at, after)) = (window[0], window[1]);
            if (before.is_lowercase() || before.is_ascii_digit()) && after.is_uppercase() {
                words.push(&piece[start..at]);
                start = at;
            }
        }
        words.push(&piece[start..]);
    }
    words.retain(|word| !word.is_empty());
    if words.is_empty() {
        words.push(name);
    }
    words
}

fn upper_first(word: &str) -> String {
    let mut chars = word.chars();
    chars.next().map_or_else(String::new, |first| {
        first.to_uppercase().chain(chars).collect()
    })
}

fn lower_first(word: &str) -> String {
    let mut chars = word.chars();
    chars.next().map_or_else(String::new, |first| {
        first.to_lowercase().chain(chars).collect()
    })
}

/// A name that breaks a rule, and what the rule would have it be.
#[derive(Clone, Debug)]
pub(super) struct Violation {
    pub diagnostic: AnalyzerDiagnostic,
    pub fixed: String,
}

/// IDE1006 for every declaration of the file whose name breaks the first
/// rule that applies to it.
pub(super) fn violations(
    view: &View<'_>,
    settings: &Settings,
    found: &mut Vec<AnalyzerDiagnostic>,
) {
    found.extend(
        violations_with_names(view, settings)
            .into_iter()
            .map(|violation| violation.diagnostic),
    );
}

pub(super) fn violations_with_names(view: &View<'_>, settings: &Settings) -> Vec<Violation> {
    let rules = rules(settings);
    if rules.is_empty() {
        return Vec::new();
    }
    let configured = settings.severity("IDE1006", false);
    let mut found = Vec::new();
    for declared in declarations(&view.root) {
        let Some(rule) = rules.iter().find(|rule| rule.symbols.applies_to(&declared)) else {
            continue;
        };
        let name = declared.token.value_text().to_string();
        if rule.style.accepts(&name) {
            continue;
        }
        let severity = match configured {
            Configured::Suppressed => continue,
            Configured::At(severity) => severity,
            Configured::Default => match rule.severity {
                Some(severity) => severity,
                None => continue,
            },
        };
        let fixed = rule.style.make_compliant(&name);
        if fixed == name || fixed.is_empty() {
            continue;
        }
        found.push(Violation {
            diagnostic: AnalyzerDiagnostic {
                id: "IDE1006",
                severity,
                span: declared.token.span(),
                message: format!(
                    "Naming rule violation: '{name}' does not match the rule '{}'",
                    rule.name
                ),
                unnecessary: false,
                deprecated: false,
            },
            fixed,
        });
    }
    found
}

/// Every name the file declares, with what the rules match it by.
fn declarations(root: &SyntaxNode) -> Vec<Declared> {
    let mut found = Vec::new();
    for node in root.descendants() {
        let modifiers = modifiers_of(&node);
        let identifier = || {
            node.child_tokens()
                .find(|token| token.kind() == K::IdentifierToken)
        };
        let kind = match node.kind() {
            K::ClassDeclaration | K::RecordDeclaration => "class",
            K::StructDeclaration | K::RecordStructDeclaration => "struct",
            K::InterfaceDeclaration => "interface",
            K::EnumDeclaration => "enum",
            K::DelegateDeclaration => "delegate",
            K::MethodDeclaration => {
                if modifiers.contains(&"override") || explicitly_implements(&node) {
                    continue;
                }
                "method"
            }
            K::PropertyDeclaration => {
                if modifiers.contains(&"override") || explicitly_implements(&node) {
                    continue;
                }
                "property"
            }
            K::EventDeclaration => {
                if modifiers.contains(&"override") || explicitly_implements(&node) {
                    continue;
                }
                "event"
            }
            K::LocalFunctionStatement => "local_function",
            K::TypeParameter => "type_parameter",
            K::Parameter => {
                // An override's parameters are named by what it overrides.
                let owner = node.parent().and_then(|list| list.parent());
                if owner.is_some_and(|owner| {
                    modifiers_of(owner).contains(&"override") || explicitly_implements(owner)
                }) {
                    continue;
                }
                "parameter"
            }
            K::EnumMemberDeclaration => {
                if let Some(token) = identifier() {
                    found.push(Declared {
                        token,
                        kind: "field",
                        accessibility: "public",
                        modifiers: vec!["const", "static"],
                    });
                }
                continue;
            }
            K::VariableDeclarator => {
                let Some(declaration) = node.parent() else {
                    continue;
                };
                let Some(holder) = declaration.parent() else {
                    continue;
                };
                let holder_modifiers = modifiers_of(holder);
                let (kind, accessibility) = match holder.kind() {
                    K::FieldDeclaration => ("field", accessibility_of(holder, &holder_modifiers)),
                    K::EventFieldDeclaration => {
                        ("event", accessibility_of(holder, &holder_modifiers))
                    }
                    K::LocalDeclarationStatement
                    | K::ForStatement
                    | K::UsingStatement
                    | K::FixedStatement => ("local", "local"),
                    _ => continue,
                };
                if let Some(token) = identifier() {
                    found.push(Declared {
                        token,
                        kind,
                        accessibility,
                        modifiers: holder_modifiers,
                    });
                }
                continue;
            }
            K::ForEachStatement | K::CatchDeclaration | K::SingleVariableDesignation => {
                if let Some(token) = identifier() {
                    found.push(Declared {
                        token,
                        kind: "local",
                        accessibility: "local",
                        modifiers: Vec::new(),
                    });
                }
                continue;
            }
            _ => continue,
        };
        let Some(token) = identifier() else {
            continue;
        };
        let accessibility = match kind {
            "local_function" | "type_parameter" | "parameter" => "local",
            _ => accessibility_of(&node, &modifiers),
        };
        found.push(Declared {
            token,
            kind,
            accessibility,
            modifiers,
        });
    }
    found
}

/// The modifiers a declaration writes, as the rules name them.
fn modifiers_of(node: &SyntaxNode) -> Vec<&'static str> {
    node.child_tokens()
        .filter_map(|token| {
            Some(match token.kind() {
                K::PublicKeyword => "public",
                K::PrivateKeyword => "private",
                K::ProtectedKeyword => "protected",
                K::InternalKeyword => "internal",
                K::StaticKeyword => "static",
                K::ConstKeyword => "const",
                K::ReadOnlyKeyword => "readonly",
                K::AbstractKeyword => "abstract",
                K::AsyncKeyword => "async",
                K::OverrideKeyword => "override",
                _ => return None,
            })
        })
        .collect()
}

/// The accessibility a member has: what it writes, or C#'s default for
/// where it is.
fn accessibility_of(node: &SyntaxNode, modifiers: &[&'static str]) -> &'static str {
    let has = |modifier: &str| modifiers.contains(&modifier);
    if has("public") {
        return "public";
    }
    if has("protected") && has("internal") {
        return "protected_internal";
    }
    if has("private") && has("protected") {
        return "private_protected";
    }
    if has("protected") {
        return "protected";
    }
    if has("internal") {
        return "internal";
    }
    if has("private") {
        return "private";
    }
    match node.parent().map(SyntaxNode::kind) {
        Some(K::InterfaceDeclaration) => "public",
        Some(
            K::ClassDeclaration
            | K::StructDeclaration
            | K::RecordDeclaration
            | K::RecordStructDeclaration,
        ) => "private",
        _ => "internal",
    }
}

/// `void IFoo.Bar()`: a name the interface chose.
fn explicitly_implements(node: &SyntaxNode) -> bool {
    node.children()
        .any(|child| child.kind() == K::ExplicitInterfaceSpecifier)
}

impl Semantic {
    /// The naming rules' diagnostics of `path` under `settings`.
    #[must_use]
    pub fn naming_violations(
        &self,
        path: &Path,
        text: Option<&str>,
        settings: &Settings,
    ) -> Option<Vec<AnalyzerDiagnostic>> {
        let view = self.view_of(path, text)?;
        let mut found = Vec::new();
        violations(&view, settings, &mut found);
        Some(found)
    }

    /// "Fix Name Violation: X" for each naming violation at `span`: the
    /// declaration renamed, with every use, by the renamer. `references`
    /// are the assemblies the project was compiled against, which the
    /// renamer's check for conflicts compiles with.
    #[must_use]
    pub fn naming_fixes(
        &self,
        path: &Path,
        span: TextSpan,
        text: Option<&str>,
        settings: &Settings,
        references: &[(PathBuf, Arc<[u8]>)],
    ) -> Vec<CodeAction> {
        let Some(view) = self.view_of(path, text) else {
            return Vec::new();
        };
        let violations: Vec<Violation> = violations_with_names(&view, settings)
            .into_iter()
            .filter(|violation| {
                let at = violation.diagnostic.span;
                at.overlaps_with(span) || at.contains(span.start()) || at.end() == span.start()
            })
            .collect();
        drop(view);
        let mut found = Vec::new();
        for violation in violations {
            let options = RenameOptions {
                file: false,
                ..RenameOptions::default()
            };
            let Ok(renamed) = self.rename(
                path,
                violation.diagnostic.span.start(),
                &violation.fixed,
                text,
                options,
                references,
            ) else {
                continue;
            };
            if renamed.edit.is_empty() {
                continue;
            }
            found.push(CodeAction {
                title: format!("Fix Name Violation: {}", violation.fixed),
                kind: ActionKind::QuickFix,
                fixes: Some("IDE1006".to_owned()),
                edit: renamed.edit,
            });
        }
        found
    }
}

#[cfg(test)]
mod tests {
    use super::super::tests::compile;
    use super::*;

    const RULES: &str = "[*.cs]\n\
        dotnet_naming_rule.private_fields.symbols = private_fields\n\
        dotnet_naming_rule.private_fields.style = underscore_camel\n\
        dotnet_naming_rule.private_fields.severity = warning\n\
        dotnet_naming_symbols.private_fields.applicable_kinds = field\n\
        dotnet_naming_symbols.private_fields.applicable_accessibilities = private\n\
        dotnet_naming_style.underscore_camel.required_prefix = _\n\
        dotnet_naming_style.underscore_camel.capitalization = camel_case\n\
        dotnet_naming_rule.constants.symbols = constants\n\
        dotnet_naming_rule.constants.style = pascal\n\
        dotnet_naming_rule.constants.severity = suggestion\n\
        dotnet_naming_symbols.constants.applicable_kinds = field\n\
        dotnet_naming_symbols.constants.required_modifiers = const\n\
        dotnet_naming_rule.types_and_members.symbols = everything\n\
        dotnet_naming_rule.types_and_members.style = pascal\n\
        dotnet_naming_rule.types_and_members.severity = warning\n\
        dotnet_naming_symbols.everything.applicable_kinds = class, struct, interface, enum, method, property, event, delegate\n\
        dotnet_naming_style.pascal.capitalization = pascal_case\n\
        dotnet_naming_rule.interfaces.symbols = interfaces\n\
        dotnet_naming_rule.interfaces.style = begins_with_i\n\
        dotnet_naming_rule.interfaces.severity = error\n\
        dotnet_naming_rule.interfaces.priority = 1\n\
        dotnet_naming_symbols.interfaces.applicable_kinds = interface\n\
        dotnet_naming_style.begins_with_i.required_prefix = I\n\
        dotnet_naming_style.begins_with_i.capitalization = pascal_case\n";

    fn settings() -> Settings {
        crate::editorconfig::settings_from_text(RULES, "C.cs")
    }

    fn violations_of(text: &str) -> Vec<(String, String, Severity)> {
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let view = semantic.view_of(Path::new("/p/C.cs"), None).unwrap();
        violations_with_names(&view, &settings())
            .into_iter()
            .map(|violation| {
                let span = violation.diagnostic.span;
                (
                    text[span.start() as usize..span.end() as usize].to_string(),
                    violation.fixed,
                    violation.diagnostic.severity,
                )
            })
            .collect()
    }

    #[test]
    fn styles_accept_and_fix_names() {
        let camel = NamingStyle {
            prefix: "_".into(),
            suffix: String::new(),
            separator: String::new(),
            capitalization: Some(Capitalization::CamelCase),
        };
        assert!(camel.accepts("_count"));
        assert!(!camel.accepts("count"));
        assert!(!camel.accepts("_Count"));
        assert_eq!(camel.make_compliant("count"), "_count");
        assert_eq!(camel.make_compliant("Count"), "_count");
        assert_eq!(camel.make_compliant("m_itemCount"), "_itemCount");
        let pascal = NamingStyle {
            prefix: String::new(),
            suffix: String::new(),
            separator: String::new(),
            capitalization: Some(Capitalization::PascalCase),
        };
        assert_eq!(pascal.make_compliant("_max_value"), "MaxValue");
        assert_eq!(pascal.make_compliant("doWork"), "DoWork");
        let upper = NamingStyle {
            prefix: String::new(),
            suffix: String::new(),
            separator: "_".into(),
            capitalization: Some(Capitalization::AllUpper),
        };
        assert!(upper.accepts("MAX_VALUE"));
        assert_eq!(upper.make_compliant("maxValue"), "MAX_VALUE");
    }

    #[test]
    fn rules_are_tried_most_specific_first() {
        let names: Vec<String> = rules(&settings())
            .into_iter()
            .map(|rule| rule.name)
            .collect();
        assert_eq!(
            names,
            vec![
                "interfaces",
                "constants",
                "private_fields",
                "types_and_members"
            ]
        );
    }

    #[test]
    fn each_declaration_is_checked_against_its_rule() {
        let text = "interface Shape { }\n\
                    class widget : Shape {\n\
                      private int count;\n\
                      private int _total;\n\
                      private const int maxSize = 3;\n\
                      public int Size => count + _total + maxSize;\n\
                      void doWork() { }\n\
                      public override string ToString() => \"\";\n\
                    }\n";
        assert_eq!(
            violations_of(text),
            vec![
                ("Shape".to_string(), "IShape".to_string(), Severity::Error),
                (
                    "widget".to_string(),
                    "Widget".to_string(),
                    Severity::Warning
                ),
                ("count".to_string(), "_count".to_string(), Severity::Warning),
                ("maxSize".to_string(), "MaxSize".to_string(), Severity::Info),
                (
                    "doWork".to_string(),
                    "DoWork".to_string(),
                    Severity::Warning
                ),
            ]
        );
    }

    #[test]
    fn the_fix_renames_every_use() {
        let text = "class Widget {\n  private int count;\n  public int Next() { count++; return count; }\n}\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let at = text.find("count;").unwrap() as u32;
        let fixes = semantic.naming_fixes(
            Path::new("/p/C.cs"),
            TextSpan::at(at),
            None,
            &settings(),
            &[],
        );
        assert_eq!(fixes.len(), 1);
        assert_eq!(fixes[0].title, "Fix Name Violation: _count");
        let edits = &fixes[0].edit.files[0].edits;
        let fixed = crate::edit::apply(text, edits);
        assert_eq!(
            fixed,
            "class Widget {\n  private int _count;\n  public int Next() { _count++; return _count; }\n}\n"
        );
    }
}
