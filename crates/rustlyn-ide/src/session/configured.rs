//! The editor's end of `.editorconfig`, Fix All and completion filtering.
//!
//! Every question the session answers about a file is answered under the
//! `.editorconfig` settings above it: diagnostics come at the severities
//! they give, or not at all; the light bulb offers the fixes of the
//! analyzers they switch on; formatting lays out whitespace as they say
//! (see [`Session::format_options`]). [`Session::editorconfig`] hands the
//! settings themselves to an editor that wants them — for its own tab
//! width, say.

use std::path::{Path, PathBuf};

use rustlyn_diagnostics::Severity;
use rustlyn_text::TextSpan;

use super::{Changes, FileDiagnostic, Refusal, Session};
use crate::editorconfig::{Configured, Settings, settings_for};
use crate::search::{MatchKind, Pattern};
use crate::semantic::{AnalyzerDiagnostic, CodeAction, Completion, FixAllScope, Semantic};
use crate::utf16::Utf16Map;

/// A completion item that matches what has been typed, and how well.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FilteredItem {
    /// Its position in the list filtered.
    pub index: usize,
    pub kind: MatchKind,
    /// Whether every letter matched in the case it was typed in.
    pub case_sensitive: bool,
    /// The byte ranges of its filter text that matched, for highlighting.
    pub ranges: Vec<(u32, u32)>,
}

impl Session {
    /// Where a path the editor gave lives: under the root when relative.
    fn absolute(&self, path: &Path) -> PathBuf {
        if path.is_absolute() {
            path.to_path_buf()
        } else {
            self.root.join(path)
        }
    }

    /// The `.editorconfig` settings for `path`.
    pub(super) fn settings(&self, path: &Path) -> Settings {
        settings_for(&self.absolute(path))
    }

    /// Every `.editorconfig` setting that applies to `path`, keys lowercased
    /// and sorted: what the files above it say, nearer ones winning.
    #[must_use]
    pub fn editorconfig(&self, path: impl AsRef<Path>) -> Vec<(String, String)> {
        self.settings(path.as_ref())
            .iter()
            .map(|(key, value)| (key.to_owned(), value.to_owned()))
            .collect()
    }

    /// Fix All: the fix for diagnostic `code` applied to every occurrence
    /// of it in `path`, or in the whole project, as one set of changes.
    ///
    /// # Errors
    ///
    /// Fails before the project is compiled.
    pub fn fix_all(
        &self,
        path: impl AsRef<Path>,
        code: &str,
        scope: FixAllScope,
        text: Option<&str>,
    ) -> Result<Changes, Refusal> {
        let path = path.as_ref();
        let semantic = self.compiled(path)?;
        let here = self
            .text_of(&semantic, path, text)
            .ok_or(Refusal::NotOpen)?;
        let references = if code == "IDE1006" {
            self.read_references(&semantic.project().references)
        } else {
            Vec::new()
        };
        let settings_of = |file: &Path| self.settings(file);
        let edit = semantic
            .fix_all(path, code, scope, text, &settings_of, &references)
            .ok_or(Refusal::NotIndexed)?;
        Ok(self.changes_of(Some(&semantic), path, &here, &edit))
    }

    /// `items` that match `typed`, in Roslyn's order: how well each matched
    /// — the whole name, its start, the starts of its words, anywhere in it
    /// — letters in the case typed before others, then preselected items,
    /// then each item's own rank and label. Each item is matched by its
    /// filter text, or its label. With nothing typed every item stays, in
    /// the same order less the match.
    #[must_use]
    pub fn completion_filter(items: &[Completion], typed: &str) -> Vec<FilteredItem> {
        let names: Vec<&str> = items
            .iter()
            .map(|item| item.filter_text.as_deref().unwrap_or(&item.label))
            .collect();
        let mut found = filter_names(&names, typed);
        found.sort_by(|a, b| {
            let (x, y) = (&items[a.index], &items[b.index]);
            a.kind
                .cmp(&b.kind)
                .then(b.case_sensitive.cmp(&a.case_sensitive))
                .then(y.preselect.cmp(&x.preselect))
                .then(x.rank.cmp(&y.rank))
                .then(x.label.to_lowercase().cmp(&y.label.to_lowercase()))
                .then(a.index.cmp(&b.index))
        });
        found
    }
}

/// The names `typed` matches, in their order, with how each matched.
#[must_use]
pub fn filter_names(names: &[&str], typed: &str) -> Vec<FilteredItem> {
    let Some(pattern) = Pattern::new(typed) else {
        return (0..names.len())
            .map(|index| FilteredItem {
                index,
                kind: MatchKind::Exact,
                case_sensitive: true,
                ranges: Vec::new(),
            })
            .collect();
    };
    names
        .iter()
        .enumerate()
        .filter_map(|(index, name)| {
            let (kind, case_sensitive, ranges) = pattern.match_name(name)?;
            Some(FilteredItem {
                index,
                kind,
                case_sensitive,
                ranges,
            })
        })
        .collect()
}

/// The compiler's diagnostics under `settings`: each at the severity they
/// give it, those set to `none` or `silent` left out. An error stays one.
pub(super) fn configure_compiler_items(settings: &Settings, items: &mut Vec<FileDiagnostic>) {
    if settings.is_empty() {
        return;
    }
    items.retain_mut(|item| {
        match settings.severity(&item.code, item.severity == 3) {
            Configured::Suppressed => return false,
            Configured::At(severity) => item.severity = severity_number(severity),
            Configured::Default => {}
        }
        item.severity != 0 || item.unnecessary
    });
}

/// The IDE analyzers' diagnostics under `settings`, as the editor gets
/// them: a hidden one only when it marks code as unnecessary.
pub(super) fn analyzer_items(
    semantic: &Semantic,
    path: &Path,
    text: Option<&str>,
    map: &Utf16Map,
    settings: &Settings,
) -> Vec<FileDiagnostic> {
    // Nothing configured: the analyzers as they are, with nothing to add.
    if settings.is_empty() {
        return super::insight::analyzer_items(semantic, path, text, map);
    }
    semantic
        .configured_diagnostics(path, text, settings)
        .unwrap_or_default()
        .into_iter()
        .filter(|diagnostic| diagnostic.severity != Severity::Hidden || diagnostic.unnecessary)
        .map(|diagnostic: AnalyzerDiagnostic| {
            let (start, length) = map.span(diagnostic.span);
            FileDiagnostic {
                start,
                length,
                severity: severity_number(diagnostic.severity),
                code: diagnostic.id.to_string(),
                message: diagnostic.message,
                unnecessary: diagnostic.unnecessary,
                deprecated: diagnostic.deprecated,
            }
        })
        .collect()
}

/// The light bulb's entries that only exist under the file's settings.
pub(super) fn extra_actions(
    session: &Session,
    semantic: &Semantic,
    path: &Path,
    span: TextSpan,
    text: Option<&str>,
) -> Vec<CodeAction> {
    let settings = session.settings(path);
    if settings.is_empty() {
        return Vec::new();
    }
    let has_rules = settings
        .iter()
        .any(|(key, _)| key.starts_with("dotnet_naming_rule."));
    let references = if has_rules {
        session.read_references(&semantic.project().references)
    } else {
        Vec::new()
    };
    semantic.configured_actions(path, span, text, &settings, &references)
}

const fn severity_number(severity: Severity) -> u8 {
    match severity {
        Severity::Hidden => 0,
        Severity::Info => 1,
        Severity::Warning => 2,
        Severity::Error => 3,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A compiled session over files written to a fresh directory, with an
    /// `.editorconfig` at its root.
    fn compiled(name: &str, editorconfig: &str, files: &[(&str, &str)]) -> (Session, PathBuf) {
        let dir = std::env::temp_dir().join(format!(
            "rustlyn-configured-{name}-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            dir.join(".editorconfig"),
            format!("root = true\n[*.cs]\n{editorconfig}"),
        )
        .unwrap();
        let mut paths = Vec::new();
        for (file, text) in files {
            let path = dir.join(file);
            std::fs::write(&path, text).unwrap();
            paths.push(path);
        }
        let session = Session::new(&dir, None, Vec::new());
        session.compile(&paths);
        (session, dir)
    }

    #[test]
    fn the_settings_of_a_file_are_handed_out() {
        let (session, dir) = compiled(
            "settings",
            "indent_size = 2\n",
            &[("A.cs", "class A { }\n")],
        );
        let settings = session.editorconfig(dir.join("A.cs"));
        assert!(settings.contains(&("indent_size".to_string(), "2".to_string())));
        assert!(session.editorconfig(dir.join("A.txt")).is_empty());
        assert_eq!(
            session.format_options(dir.join("A.cs"), None).indent_size,
            2
        );
        std::fs::remove_dir_all(dir).ok();
    }

    #[test]
    fn diagnostics_come_at_the_configured_severity() {
        let text = "class A {\n  private int unused;\n  void M() { int x; var y = 1; }\n}\n";
        let (session, dir) = compiled(
            "severity",
            "dotnet_diagnostic.IDE0051.severity = none\n\
             dotnet_diagnostic.CS0168.severity = error\n\
             csharp_style_var_for_built_in_types = false:warning\n",
            &[("A.cs", text)],
        );
        let found = session.diagnostics(dir.join("A.cs"), None).unwrap();
        let codes: Vec<(&str, u8)> = found
            .items
            .iter()
            .map(|item| (item.code.as_str(), item.severity))
            .collect();
        assert!(
            !codes.iter().any(|(code, _)| *code == "IDE0051"),
            "{codes:?}"
        );
        assert!(codes.contains(&("CS0168", 3)), "{codes:?}");
        assert!(codes.contains(&("IDE0008", 2)), "{codes:?}");
        std::fs::remove_dir_all(dir).ok();
    }

    #[test]
    fn the_light_bulb_and_fix_all_follow_the_settings() {
        let text =
            "class A {\n  void M() { var a = 1; var b = 2; System.Console.WriteLine(a + b); }\n}\n";
        let (session, dir) = compiled(
            "fixes",
            "csharp_style_var_for_built_in_types = false:suggestion\n",
            &[("A.cs", text)],
        );
        let path = dir.join("A.cs");
        let at = text.find("var a").unwrap() as u32;
        let actions = session.code_actions(&path, at, at, None).unwrap();
        assert!(
            actions
                .iter()
                .any(|action| action.fixes.as_deref() == Some("IDE0008")),
            "{actions:?}"
        );
        let changes = session
            .fix_all(&path, "IDE0008", FixAllScope::Document, None)
            .unwrap();
        let mut fixed = text.to_string();
        for change in changes.changes.iter().rev() {
            fixed.replace_range(
                change.start as usize..(change.start + change.length) as usize,
                &change.text,
            );
        }
        assert_eq!(
            fixed,
            "class A {\n  void M() { int a = 1; int b = 2; System.Console.WriteLine(a + b); }\n}\n"
        );
        std::fs::remove_dir_all(dir).ok();
    }

    /// A file of about a thousand lines: fields, properties and methods
    /// with locals, loops and calls.
    fn large_file() -> String {
        let mut text = String::from(
            "using System;\nusing System.Collections.Generic;\n\nnamespace Game\n{\n    public class Board\n    {\n",
        );
        for index in 0..58 {
            text.push_str(&format!(
                "        private int count{index};\n        public int Size{index} {{ get {{ return count{index}; }} }}\n\n        public int Step{index}(int limit, string name)\n        {{\n            int total = 0;\n            var items = new List<int>();\n            for (int i = 0; i < limit; i++)\n            {{\n                items.Add(i * {index});\n                total += i;\n            }}\n            string label = name + total;\n            Console.WriteLine(label);\n            count{index} = total;\n            return total + items.Count;\n        }}\n\n"
            ));
        }
        text.push_str("    }\n}\n");
        text
    }

    /// Not a check but a measurement: `cargo test -p rustlyn-ide --lib
    /// diagnostics_of_a_large_file -- --ignored --nocapture`. Prints how long
    /// the session's diagnostics take for a thousand-line file with no
    /// `.editorconfig`, with one that switches on every configured
    /// analyzer, and what the compiler and the analyzers took on their own
    /// before any of this existed.
    #[test]
    #[ignore = "a measurement, run by hand"]
    fn diagnostics_of_a_large_file() {
        let text = large_file();
        assert!(text.lines().count() > 1000, "{}", text.lines().count());
        let config = "csharp_style_var_for_built_in_types = false:suggestion\n\
                      csharp_style_var_when_type_is_apparent = true:suggestion\n\
                      csharp_style_var_elsewhere = false:suggestion\n\
                      csharp_style_expression_bodied_methods = when_on_single_line:suggestion\n\
                      csharp_style_expression_bodied_properties = true:suggestion\n\
                      dotnet_style_qualification_for_field = true:suggestion\n\
                      dotnet_naming_rule.fields.symbols = fields\n\
                      dotnet_naming_rule.fields.style = underscore\n\
                      dotnet_naming_rule.fields.severity = warning\n\
                      dotnet_naming_symbols.fields.applicable_kinds = field\n\
                      dotnet_naming_style.underscore.required_prefix = _\n\
                      dotnet_naming_style.underscore.capitalization = camel_case\n";
        let time = |label: &str, run: &dyn Fn() -> usize| {
            let _ = run();
            let rounds = 5u32;
            let started = std::time::Instant::now();
            let mut found = 0;
            for _ in 0..rounds {
                found = run();
            }
            let each = started.elapsed() / rounds;
            println!("{label}: {each:?} ({found} diagnostics)");
            each
        };
        let (plain, dir) = compiled("large-plain", "", &[("Board.cs", &text)]);
        let path = dir.join("Board.cs");
        std::fs::remove_file(dir.join(".editorconfig")).ok();
        let semantic = plain.compiled(&path).expect("compiled");
        let before = time("compiler and analyzers alone (as before)", &|| {
            semantic.diagnostics(&path, Some(&text)).unwrap().len()
                + semantic
                    .analyzer_diagnostics(&path, Some(&text))
                    .unwrap()
                    .len()
        });
        let unconfigured = time("session, no .editorconfig", &|| {
            plain.diagnostics(&path, Some(&text)).unwrap().items.len()
        });
        let (configured, other) = compiled("large-configured", config, &[("Board.cs", &text)]);
        let other_path = other.join("Board.cs");
        let with_settings = time("session, every configured analyzer on", &|| {
            configured
                .diagnostics(&other_path, Some(&text))
                .unwrap()
                .items
                .len()
        });
        println!(
            "ratio: {:.2}x unconfigured, {:.2}x configured",
            unconfigured.as_secs_f64() / before.as_secs_f64(),
            with_settings.as_secs_f64() / before.as_secs_f64()
        );
        std::fs::remove_dir_all(dir).ok();
        std::fs::remove_dir_all(other).ok();
    }

    #[test]
    fn completion_is_filtered_the_way_roslyn_orders_it() {
        let names = [
            "GetHashCode",
            "GoToDefinition",
            "Gtd",
            "gtdLower",
            "Other",
            "ToString",
        ];
        let found = filter_names(&names, "gtd");
        let order: Vec<&str> = found.iter().map(|item| names[item.index]).collect();
        assert!(order.contains(&"GoToDefinition"));
        assert!(!order.contains(&"Other"));
        let items: Vec<Completion> = names
            .iter()
            .map(|name| Completion {
                label: (*name).to_string(),
                kind: crate::semantic::CompletionKind::Method,
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
            })
            .collect();
        let sorted = Session::completion_filter(&items, "Gtd");
        let first = sorted.first().expect("a match");
        assert_eq!(items[first.index].label, "Gtd");
        let camel = Session::completion_filter(&items, "GTD");
        assert!(
            camel
                .iter()
                .any(|item| items[item.index].label == "GoToDefinition"
                    && item.kind == MatchKind::CamelCaseExact),
            "{camel:?}"
        );
        assert_eq!(Session::completion_filter(&items, "").len(), items.len());
    }
}
