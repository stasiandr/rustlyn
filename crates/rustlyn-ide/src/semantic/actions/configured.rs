//! The fixes of the analyzers an `.editorconfig` switches on, and Fix All.
//!
//! The code-style analyzers — `var` or not, expression body or not, `this.`
//! or not, naming rules — answer a preference, and their fixes are the
//! refactorings that already rewrite the code either way: IDE0007's fix is
//! "Use 'var'", offered under the diagnostic's id. IDE1006's fix renames,
//! so it is made by the renamer and needs the assemblies the project was
//! compiled against.
//!
//! Fix All is Roslyn's `FixAllProvider` for all of them and for the
//! compiler's and the other analyzers' diagnostics: the same fix applied to
//! every occurrence of a diagnostic in a document or the whole project. Each
//! occurrence's fix is worked out the way the light bulb would work it out;
//! fixes whose edits do not touch each other are applied together, and the
//! ones that would collide with an edit already taken wait for the next
//! round, which works everything out again on the text the first round
//! left. That is what makes "add every missing `using`" work, where each
//! fix inserts at the same place, and what keeps two removals of
//! neighbouring declarations from tearing each other's lines apart.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use rustlyn_diagnostics::Diagnostic;
use rustlyn_syntax::SyntaxKind;
use rustlyn_text::TextSpan;

use super::{ActionKind, CodeAction, Context, analyzer_fixes, fixes, refactorings};
use crate::edit::{TextEdit, WorkspaceEdit};
use crate::editorconfig::Settings;
use crate::semantic::{AnalyzerDiagnostic, Semantic, View};

/// How far Fix All reaches.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum FixAllScope {
    /// The one document asked about.
    Document = 0,
    /// Every document of the project.
    Project = 1,
}

/// The ids of the analyzers only an `.editorconfig` switches on, whose
/// fixes are here rather than with the other analyzers'.
const STYLE_IDS: &[&str] = &[
    "IDE0007", "IDE0008", "IDE0009", "IDE0021", "IDE0022", "IDE0023", "IDE0024", "IDE0025",
    "IDE0026", "IDE0027", "IDE0061",
];

/// At most this many rounds of Fix All: each round applies every fix that
/// does not collide with another, so a round that makes no progress ends
/// it well before.
const ROUNDS: usize = 16;

fn touches(at: TextSpan, span: TextSpan) -> bool {
    at.overlaps_with(span)
        || at.contains(span.start())
        || span.contains(at.start())
        || at.end() == span.start()
}

/// The fix of a code-style diagnostic: the refactoring that makes the code
/// what the preference says, under the diagnostic's id.
fn style_fix(context: &mut Context<'_, '_>, diagnostic: &AnalyzerDiagnostic) -> Option<CodeAction> {
    if diagnostic.id == "IDE0009" {
        return Some(context.local(
            "Add 'this.' qualification",
            ActionKind::QuickFix,
            Some("IDE0009"),
            vec![TextEdit::insert(diagnostic.span.start(), "this.")],
        ));
    }
    let wanted = match diagnostic.id {
        "IDE0007" => "Use 'var'".to_owned(),
        "IDE0008" => "Use explicit type".to_owned(),
        _ => diagnostic.message.clone(),
    };
    context.span = TextSpan::at(diagnostic.span.start());
    let mut offered = Vec::new();
    refactorings::collect_style(context, &mut offered);
    offered
        .into_iter()
        .find(|action| action.title == wanted)
        .map(|mut action| {
            action.kind = ActionKind::QuickFix;
            action.fixes = Some(diagnostic.id.to_owned());
            action
        })
}

/// A diagnostic of one kind, in one place: what Fix All fixes one of.
#[derive(Clone, Debug)]
enum Occurrence {
    Compiler(Diagnostic),
    Analyzer(AnalyzerDiagnostic),
    /// A `switch` Roslyn's IDE0010 or IDE0072 is about, by its keyword.
    Switch(TextSpan),
}

impl Occurrence {
    fn span(&self) -> TextSpan {
        match self {
            Self::Compiler(diagnostic) => diagnostic.span(),
            Self::Analyzer(diagnostic) => diagnostic.span,
            Self::Switch(span) => *span,
        }
    }
}

impl Semantic {
    /// The fixes for the diagnostics at `span` that only exist under
    /// `settings`: the code-style analyzers' and the naming rules'. The
    /// light bulb offers them with [`Semantic::code_actions`]' own.
    #[must_use]
    pub fn configured_actions(
        &self,
        path: &Path,
        span: TextSpan,
        text: Option<&str>,
        settings: &Settings,
        references: &[(PathBuf, Arc<[u8]>)],
    ) -> Vec<CodeAction> {
        let Some(current) = text
            .map(str::to_owned)
            .or_else(|| self.text(path).map(str::to_owned))
        else {
            return Vec::new();
        };
        let mut found = Vec::new();
        let style: Vec<AnalyzerDiagnostic> = self
            .configured_diagnostics(path, text, settings)
            .unwrap_or_default()
            .into_iter()
            .filter(|diagnostic| {
                STYLE_IDS.contains(&diagnostic.id) && touches(diagnostic.span, span)
            })
            .collect();
        if !style.is_empty()
            && let Some(mut view) = self.view_of(path, text)
        {
            for diagnostic in &style {
                let mut context = Context {
                    view: &mut view,
                    path: path.to_path_buf(),
                    text: current.clone(),
                    span,
                    diagnostics: Vec::new(),
                };
                found.extend(style_fix(&mut context, diagnostic));
            }
        }
        found.extend(self.naming_fixes(path, span, text, settings, references));
        found.retain(|action| !action.edit.is_empty());
        let mut seen = std::collections::HashSet::new();
        found.retain(|action| seen.insert(action.title.clone()));
        found
    }

    /// Fix All: the fix for diagnostic `code` applied to every occurrence
    /// of it in `path`, or in the whole project. Spans count in `text` for
    /// `path` and in the compiled text for every other file. `settings_of`
    /// gives each file's `.editorconfig` settings; `references` are what
    /// the renamer compiles with, for IDE1006.
    ///
    /// Supported: every fix the light bulb has for a compiler diagnostic
    /// (a missing `using`, ...), every IDE analyzer fix (unused members,
    /// values and variables, casts, names to simplify, `this.`), IDE0005
    /// unnecessary usings, IDE0010 and IDE0072 populate `switch`, the
    /// code-style fixes and IDE1006 naming.
    #[must_use]
    pub fn fix_all(
        &self,
        path: &Path,
        code: &str,
        scope: FixAllScope,
        text: Option<&str>,
        settings_of: &dyn Fn(&Path) -> Settings,
        references: &[(PathBuf, Arc<[u8]>)],
    ) -> Option<WorkspaceEdit> {
        let asked = match text {
            Some(text) => text.to_owned(),
            None => self.text(path)?.to_owned(),
        };
        let mut files: Vec<PathBuf> = match scope {
            FixAllScope::Document => vec![path.to_path_buf()],
            FixAllScope::Project => {
                let mut all: Vec<PathBuf> = self.paths.values().cloned().collect();
                all.sort();
                all
            }
        };
        if !files.iter().any(|file| file == path) {
            files.insert(0, path.to_path_buf());
        }
        let mut external: BTreeMap<PathBuf, Vec<TextEdit>> = BTreeMap::new();
        let mut finished: Vec<(PathBuf, String, String)> = Vec::new();
        for file in files {
            let original = if file == path {
                asked.clone()
            } else {
                let Some(text) = self.text(&file) else {
                    continue;
                };
                text.to_owned()
            };
            let settings = settings_of(&file);
            let fixed =
                self.fix_document(&file, &original, code, &settings, references, &mut external);
            finished.push((file, original, fixed));
        }

        let mut edit = WorkspaceEdit::default();
        for (file, original, fixed) in finished {
            let mut edits = line_diff(&original, &fixed);
            // Edits made from another file count in this one's compiled
            // text, which is the text asked about only when the editor has
            // not changed it.
            let compiled_is_original = self.text(&file) == Some(original.as_str());
            if let Some(more) = external.remove(&file)
                && compiled_is_original
            {
                for one in more {
                    if !edits.contains(&one) && !edits.iter().any(|taken| clashes(taken, &one)) {
                        edits.push(one);
                    }
                }
            }
            if !edits.is_empty() {
                edit.add_all(file, edits);
            }
        }
        for (file, edits) in external {
            if file != path {
                edit.add_all(file, edits);
            }
        }
        Some(edit)
    }

    /// Fixes every occurrence of `code` in one file, round after round, and
    /// gives back the file's text once fixed. Edits a fix makes to other
    /// files — a rename's — are gathered in `external`, in those files'
    /// compiled text.
    fn fix_document(
        &self,
        path: &Path,
        original: &str,
        code: &str,
        settings: &Settings,
        references: &[(PathBuf, Arc<[u8]>)],
        external: &mut BTreeMap<PathBuf, Vec<TextEdit>>,
    ) -> String {
        let mut current = original.to_owned();
        // Roslyn's equivalence key: the title of the first fix chosen, which
        // later occurrences prefer when they are offered it too.
        let mut chosen: Option<String> = None;
        for _ in 0..ROUNDS {
            let occurrences = self.occurrences(path, &current, code, settings);
            if occurrences.is_empty() {
                break;
            }
            let actions = crate::editorconfig::with_code_style(settings.code_style(), || {
                self.actions_for(
                    path,
                    &current,
                    code,
                    &occurrences,
                    settings,
                    references,
                    &mut chosen,
                )
            });
            let mut taken: Vec<TextEdit> = Vec::new();
            let mut progressed = false;
            for action in actions {
                let mine: Vec<&TextEdit> = action.edit.edits_of(path).iter().collect();
                let others: Vec<(&PathBuf, &TextEdit)> = action
                    .edit
                    .files
                    .iter()
                    .filter(|file| file.path != path)
                    .flat_map(|file| file.edits.iter().map(move |one| (&file.path, one)))
                    .collect();
                let collides = mine.iter().any(|one| {
                    !taken.contains(one) && taken.iter().any(|other| clashes(other, one))
                }) || others.iter().any(|(file, one)| {
                    external.get(*file).is_some_and(|there| {
                        !there.contains(one) && there.iter().any(|other| clashes(other, one))
                    })
                });
                if collides {
                    continue;
                }
                for one in mine {
                    if !taken.contains(one) {
                        taken.push(one.clone());
                        progressed = true;
                    }
                }
                for (file, one) in others {
                    let there = external.entry(file.clone()).or_default();
                    if !there.contains(one) {
                        there.push(one.clone());
                        progressed = true;
                    }
                }
            }
            if !progressed || taken.is_empty() {
                break;
            }
            current = crate::edit::apply(&current, &taken);
        }
        current
    }

    /// Every occurrence of `code` in `path` as it reads in `current`.
    fn occurrences(
        &self,
        path: &Path,
        current: &str,
        code: &str,
        settings: &Settings,
    ) -> Vec<Occurrence> {
        if code == "IDE0010" || code == "IDE0072" {
            let Some(view) = self.view_of(path, Some(current)) else {
                return Vec::new();
            };
            let kind = if code == "IDE0010" {
                SyntaxKind::SwitchStatement
            } else {
                SyntaxKind::SwitchExpression
            };
            return view
                .root
                .descendants()
                .filter(|node| node.kind() == kind)
                .filter_map(|node| node.child_token_of_kind(SyntaxKind::SwitchKeyword))
                .map(|keyword| Occurrence::Switch(keyword.span()))
                .collect();
        }
        let mut found: Vec<Occurrence> = self
            .diagnostics(path, Some(current))
            .unwrap_or_default()
            .into_iter()
            .filter(|diagnostic| diagnostic.code().to_string() == code)
            .map(Occurrence::Compiler)
            .collect();
        let analyzed: Vec<Occurrence> = self
            .configured_diagnostics(path, Some(current), settings)
            .unwrap_or_default()
            .into_iter()
            .filter(|diagnostic| diagnostic.id == code)
            .map(Occurrence::Analyzer)
            .collect();
        for occurrence in analyzed {
            if !found.iter().any(|other| other.span() == occurrence.span()) {
                found.push(occurrence);
            }
        }
        found.sort_by_key(|occurrence| (occurrence.span().start(), occurrence.span().end()));
        found
    }

    /// The fix chosen for each occurrence, in order.
    #[allow(clippy::too_many_arguments)]
    fn actions_for(
        &self,
        path: &Path,
        current: &str,
        code: &str,
        occurrences: &[Occurrence],
        settings: &Settings,
        references: &[(PathBuf, Arc<[u8]>)],
        chosen: &mut Option<String>,
    ) -> Vec<CodeAction> {
        let mut found = Vec::new();
        if code == "IDE1006" {
            for occurrence in occurrences {
                let offered = self.naming_fixes(
                    path,
                    TextSpan::at(occurrence.span().start()),
                    Some(current),
                    settings,
                    references,
                );
                found.extend(pick(offered, code, chosen));
            }
            return found;
        }
        let Some(mut view) = self.view_of(path, Some(current)) else {
            return found;
        };
        for occurrence in occurrences {
            let offered = one_fix(&mut view, path, current, code, occurrence);
            found.extend(pick(offered, code, chosen));
        }
        found
    }
}

/// What the light bulb would offer for one occurrence.
fn one_fix(
    view: &mut View<'_>,
    path: &Path,
    current: &str,
    code: &str,
    occurrence: &Occurrence,
) -> Vec<CodeAction> {
    let mut context = Context {
        view,
        path: path.to_path_buf(),
        text: current.to_owned(),
        span: TextSpan::at(occurrence.span().start()),
        diagnostics: Vec::new(),
    };
    let mut offered = Vec::new();
    match occurrence {
        Occurrence::Compiler(diagnostic) => {
            context.span = diagnostic.span();
            context.diagnostics = vec![diagnostic.clone()];
            fixes::collect(&mut context, &mut offered);
        }
        Occurrence::Analyzer(diagnostic) if code == "IDE0005" => {
            context.span = diagnostic.span;
            refactorings::collect(&mut context, &mut offered);
            offered.retain(|action| action.title == "Remove unnecessary usings");
            for action in &mut offered {
                action.fixes = Some("IDE0005".to_owned());
            }
        }
        Occurrence::Analyzer(diagnostic) if STYLE_IDS.contains(&diagnostic.id) => {
            offered.extend(style_fix(&mut context, diagnostic));
        }
        Occurrence::Analyzer(diagnostic) => {
            context.span = diagnostic.span;
            offered.extend(analyzer_fixes::fix(&mut context, diagnostic));
        }
        Occurrence::Switch(_) => fixes::collect(&mut context, &mut offered),
    }
    offered
}

/// The action for an occurrence: one that fixes `code`, the one titled as
/// the first choice was when there is one.
fn pick(offered: Vec<CodeAction>, code: &str, chosen: &mut Option<String>) -> Option<CodeAction> {
    let fitting: Vec<CodeAction> = offered
        .into_iter()
        .filter(|action| action.fixes.as_deref() == Some(code) && !action.edit.is_empty())
        .collect();
    let action = chosen
        .as_ref()
        .and_then(|title| {
            fitting
                .iter()
                .find(|action| &action.title == title)
                .cloned()
        })
        .or_else(|| fitting.into_iter().next())?;
    if chosen.is_none() {
        *chosen = Some(action.title.clone());
    }
    Some(action)
}

/// Whether two edits cannot both be applied: they overlap, or both insert
/// at, or one inserts inside, the same place. Adjacent edits are fine.
fn clashes(a: &TextEdit, b: &TextEdit) -> bool {
    let (a, b) = (a.span, b.span);
    if a.start() == b.start() {
        return true;
    }
    if a.is_empty() {
        return a.start() > b.start() && a.start() < b.end();
    }
    if b.is_empty() {
        return b.start() > a.start() && b.start() < a.end();
    }
    a.start() < b.end() && b.start() < a.end()
}

/// The edits that turn `old` into `new`, a stretch of changed lines each:
/// a fix of one line reads as an edit of that line, not of everything from
/// the first change to the last.
fn line_diff(old: &str, new: &str) -> Vec<TextEdit> {
    if old == new {
        return Vec::new();
    }
    let a: Vec<&str> = old.split_inclusive('\n').collect();
    let b: Vec<&str> = new.split_inclusive('\n').collect();
    let prefix = a.iter().zip(&b).take_while(|(x, y)| x == y).count();
    let suffix = a[prefix..]
        .iter()
        .rev()
        .zip(b[prefix..].iter().rev())
        .take_while(|(x, y)| x == y)
        .count();
    let (a_mid, b_mid) = (&a[prefix..a.len() - suffix], &b[prefix..b.len() - suffix]);
    let start_of = |lines: &[&str], index: usize| -> usize {
        lines[..index].iter().map(|line| line.len()).sum()
    };
    let base = start_of(&a, prefix);
    // Too large to compare line by line: one edit for the middle.
    if a_mid.len() * b_mid.len() > 4_000_000 {
        let end = base + a_mid.iter().map(|line| line.len()).sum::<usize>();
        return vec![TextEdit::new(
            TextSpan::from_bounds(base as u32, end as u32),
            b_mid.concat(),
        )];
    }
    // The longest common subsequence of lines, and the stretches between.
    let (n, m) = (a_mid.len(), b_mid.len());
    let mut table = vec![0u32; (n + 1) * (m + 1)];
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            table[i * (m + 1) + j] = if a_mid[i] == b_mid[j] {
                table[(i + 1) * (m + 1) + j + 1] + 1
            } else {
                table[(i + 1) * (m + 1) + j].max(table[i * (m + 1) + j + 1])
            };
        }
    }
    let mut edits = Vec::new();
    let (mut i, mut j) = (0, 0);
    let mut offset = base;
    let mut pending: Option<(usize, usize, String)> = None;
    let flush = |pending: &mut Option<(usize, usize, String)>, edits: &mut Vec<TextEdit>| {
        if let Some((start, end, text)) = pending.take() {
            edits.push(TextEdit::new(
                TextSpan::from_bounds(start as u32, end as u32),
                text,
            ));
        }
    };
    while i < n || j < m {
        if i < n && j < m && a_mid[i] == b_mid[j] {
            flush(&mut pending, &mut edits);
            offset += a_mid[i].len();
            i += 1;
            j += 1;
        } else if j < m && (i == n || table[i * (m + 1) + j + 1] >= table[(i + 1) * (m + 1) + j]) {
            let entry = pending.get_or_insert((offset, offset, String::new()));
            entry.2.push_str(b_mid[j]);
            j += 1;
        } else {
            let entry = pending.get_or_insert((offset, offset, String::new()));
            entry.1 += a_mid[i].len();
            offset += a_mid[i].len();
            i += 1;
        }
    }
    flush(&mut pending, &mut edits);
    edits
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::super::super::tests::compile;
    use super::*;

    /// `text` with every occurrence of `code` fixed.
    fn fix_all(text: &str, code: &str, config: &str) -> String {
        fix_all_with(text, &[], code, config)
    }

    /// The same, with other files in the project.
    fn fix_all_with(text: &str, others: &[(&str, &str)], code: &str, config: &str) -> String {
        let mut files = vec![("C.cs", text)];
        files.extend_from_slice(others);
        let semantic = compile(&files, false).expect("compiled");
        let settings =
            crate::editorconfig::settings_from_text(&format!("[*.cs]\n{config}"), "C.cs");
        let settings_of = move |_: &Path| settings.clone();
        let edit = semantic
            .fix_all(
                Path::new("/p/C.cs"),
                code,
                FixAllScope::Document,
                None,
                &settings_of,
                &[],
            )
            .expect("fixed");
        crate::edit::apply(text, edit.edits_of(Path::new("/p/C.cs")))
    }

    #[test]
    fn line_diff_keeps_edits_to_the_lines_that_changed() {
        let old = "a\nb\nc\nd\n";
        let new = "a\nB\nc\nd\ne\n";
        let edits = line_diff(old, new);
        assert_eq!(edits.len(), 2);
        assert_eq!(crate::edit::apply(old, &edits), new);
        assert_eq!(crate::edit::apply("x\n", &line_diff("x\n", "")), "");
    }

    #[test]
    fn every_unused_variable_goes() {
        let text = "class C {\n  int M() {\n    int a;\n    int b = 2;\n    int c;\n    return 1;\n  }\n}\n";
        let fixed = fix_all(text, "CS0168", "");
        assert!(
            !fixed.contains("int a;") && !fixed.contains("int c;"),
            "{fixed}"
        );
        assert!(fixed.contains("int b = 2;"), "{fixed}");
        let both = fix_all(&fixed, "CS0219", "");
        assert_eq!(both, "class C {\n  int M() {\n    return 1;\n  }\n}\n");
    }

    #[test]
    fn every_unused_member_and_cast_goes() {
        let text = "class C {\n  private int a;\n  private void B() { }\n  public int D(int x) => (int)x + (int)x;\n}\n";
        let fixed = fix_all(text, "IDE0051", "");
        assert_eq!(
            fixed,
            "class C {\n  public int D(int x) => (int)x + (int)x;\n}\n"
        );
        let casts = fix_all(&fixed, "IDE0004", "");
        assert_eq!(casts, "class C {\n  public int D(int x) => x + x;\n}\n");
    }

    #[test]
    fn every_missing_using_is_added() {
        let library = "namespace System.Text { public class StringBuilder { } }\n\
                       namespace Game.Things { public class Widget { } }\n";
        let text = "class C {\n  void M() {\n    var b = new StringBuilder();\n    var w = new Widget();\n    var s = new StringBuilder();\n  }\n}\n";
        let fixed = fix_all_with(text, &[("Lib.cs", library)], "CS0246", "");
        assert!(fixed.contains("using System.Text;"), "{fixed}");
        assert!(fixed.contains("using Game.Things;"), "{fixed}");
        assert_eq!(fixed.matches("using System.Text;").count(), 1, "{fixed}");
    }

    #[test]
    fn usings_and_namespaces_follow_the_code_style() {
        let library = "namespace Game.Things { public class Widget { } }\n\
                       namespace System.Text { public class StringBuilder { } }\n";
        // Inside the namespace, when that is where the settings want them.
        let text = "namespace App\n{\n    class C { object M() => new Widget(); }\n}\n";
        let fixed = fix_all_with(
            text,
            &[("Lib.cs", library)],
            "CS0246",
            "csharp_using_directive_placement = inside_namespace\n",
        );
        assert_eq!(
            fixed,
            "namespace App\n{\n    using Game.Things;\n\n    class C { object M() => new Widget(); }\n}\n"
        );
        // `System` sorted with the rest.
        let text = "using Alpha;\nusing Zeta;\nclass C { object M() => new StringBuilder(); }\nnamespace Alpha { class A { } }\nnamespace Zeta { class Z { } }\n";
        let unsorted = fix_all_with(
            text,
            &[("Lib.cs", library)],
            "CS0246",
            "dotnet_sort_system_directives_first = false\n",
        );
        assert!(
            unsorted.starts_with("using Alpha;\nusing System.Text;\nusing Zeta;\n"),
            "{unsorted}"
        );
        let sorted = fix_all_with(text, &[("Lib.cs", library)], "CS0246", "");
        assert!(
            sorted.starts_with("using System.Text;\nusing Alpha;\n"),
            "{sorted}"
        );

        // A new file takes the namespace style the settings prefer.
        let source = "namespace App.Models\n{\n    class C\n    {\n        Widget w = new Widget();\n    }\n}\n";
        let semantic = compile(&[("C.cs", source)], false).expect("compiled");
        let at = source.find("Widget w").unwrap() as u32;
        let style = crate::editorconfig::settings_from_text(
            "[*.cs]\ncsharp_style_namespace_declarations = file_scoped\n",
            "C.cs",
        )
        .code_style();
        let actions = crate::editorconfig::with_code_style(style, || {
            semantic.code_actions(Path::new("/p/C.cs"), TextSpan::at(at), None)
        })
        .expect("actions");
        let generated = actions
            .iter()
            .find(|action| action.title == "Generate class 'Widget' in new file")
            .expect("offered");
        let made = crate::edit::apply("", &generated.edit.files[0].edits);
        assert!(made.starts_with("namespace App.Models;\n"), "{made}");
    }

    #[test]
    fn every_name_is_simplified_and_every_unread_value_goes() {
        let text = "class C {\n  static int count;\n  static void Log() { }\n  void M() { C.Log(); var x = C.count; C.Log(); System.Console.WriteLine(x); }\n}\n";
        assert_eq!(
            fix_all(text, "IDE0002", ""),
            "class C {\n  static int count;\n  static void Log() { }\n  void M() { Log(); var x = count; Log(); System.Console.WriteLine(x); }\n}\n"
        );
        let values = "class C {\n  int M(int a) {\n    int x = 1;\n    x = 2;\n    int y = a;\n    y = 3;\n    return x + y;\n  }\n}\n";
        let fixed = fix_all(values, "IDE0059", "");
        assert!(
            !fixed.contains("= 1;") && !fixed.contains("y = a"),
            "{fixed}"
        );
        assert!(
            fixed.contains("x = 2;") && fixed.contains("y = 3;"),
            "{fixed}"
        );
    }

    #[test]
    fn unnecessary_usings_go_at_once() {
        let library = "namespace Game.Things { public class Widget { } }\n";
        let text =
            "using System;\nusing Game.Things;\nusing System.Collections.Generic;\nclass C { }\n";
        assert_eq!(
            fix_all_with(text, &[("Lib.cs", library)], "IDE0005", ""),
            "class C { }\n"
        );
    }

    #[test]
    fn every_switch_is_populated() {
        let text = "enum Color { Red, Green }\n\
                    class C {\n\
                      void M(Color a, Color b) {\n\
                        switch (a) { case Color.Red: break; }\n\
                        switch (b) { }\n\
                      }\n\
                    }\n";
        let fixed = fix_all(text, "IDE0010", "");
        assert_eq!(fixed.matches("case Color.Green:").count(), 2, "{fixed}");
    }

    #[test]
    fn var_preferences_are_applied_everywhere() {
        let text = "class C {\n  void M() {\n    int a = 1;\n    string s = \"\";\n    System.Console.WriteLine(a + s);\n  }\n}\n";
        let fixed = fix_all(
            text,
            "IDE0007",
            "csharp_style_var_for_built_in_types = true\n",
        );
        assert_eq!(
            fixed,
            "class C {\n  void M() {\n    var a = 1;\n    var s = \"\";\n    System.Console.WriteLine(a + s);\n  }\n}\n"
        );
        let back = fix_all(
            &fixed,
            "IDE0008",
            "csharp_style_var_for_built_in_types = false\n",
        );
        assert_eq!(back, text);
    }

    #[test]
    fn every_name_breaking_a_rule_is_renamed() {
        let text = "class C {\n  private int count;\n  private int total;\n  int Sum() => count + total;\n}\n";
        let config = "dotnet_naming_rule.fields.symbols = fields\n\
                      dotnet_naming_rule.fields.style = underscore\n\
                      dotnet_naming_rule.fields.severity = warning\n\
                      dotnet_naming_symbols.fields.applicable_kinds = field\n\
                      dotnet_naming_style.underscore.required_prefix = _\n\
                      dotnet_naming_style.underscore.capitalization = camel_case\n";
        let fixed = fix_all(text, "IDE1006", config);
        assert_eq!(
            fixed,
            "class C {\n  private int _count;\n  private int _total;\n  int Sum() => _count + _total;\n}\n"
        );
    }

    #[test]
    fn the_light_bulb_offers_the_style_fixes() {
        let text = "class C {\n  int x;\n  int Get() { return x; }\n}\n";
        let semantic = compile(&[("C.cs", text)], false).expect("compiled");
        let settings = crate::editorconfig::settings_from_text(
            "[*.cs]\ncsharp_style_expression_bodied_methods = true\ndotnet_style_qualification_for_field = true\n",
            "C.cs",
        );
        let at = text.find("Get").unwrap() as u32;
        let actions = semantic.configured_actions(
            Path::new("/p/C.cs"),
            TextSpan::at(at),
            None,
            &settings,
            &[],
        );
        let titles: Vec<&str> = actions.iter().map(|action| action.title.as_str()).collect();
        assert_eq!(titles, vec!["Use expression body for method"]);
        assert_eq!(actions[0].fixes.as_deref(), Some("IDE0022"));
        let fixed = fix_all(
            text,
            "IDE0009",
            "dotnet_style_qualification_for_field = true\n",
        );
        assert!(fixed.contains("return this.x;"), "{fixed}");
    }
}
