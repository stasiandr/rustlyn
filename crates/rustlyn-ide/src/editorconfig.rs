//! `.editorconfig`: the settings a repository writes down for how its code
//! is laid out and what its analyzers say, read the way Roslyn reads them.
//!
//! A file's settings come from every `.editorconfig` between it and the
//! first one that says `root = true`, or the top of the file system. Each
//! file is a list of sections headed by a glob — `[*.cs]`, `[src/**/*.{cs,csx}]`
//! — and each section a list of `key = value` lines. The settings of a file
//! are what every section whose glob matches it says, the farther files
//! first and the nearer ones on top, and within one file the later sections
//! on top of the earlier ones. Keys are case-insensitive, and so are the
//! values the editor understands; names a rule gives itself are kept as
//! written.
//!
//! What the settings are for, and who reads them:
//!
//! * **Layout**: `indent_style`, `indent_size`, `tab_width`, `end_of_line`,
//!   `insert_final_newline` and Roslyn's `csharp_new_line_*`,
//!   `csharp_indent_*`, `csharp_space_*` and `csharp_preserve_*` become
//!   [`FormatOptions`], which the formatter honours.
//! * **Severities**: `dotnet_diagnostic.<ID>.severity`,
//!   `dotnet_analyzer_diagnostic.severity` and its per-category form decide
//!   how loudly each diagnostic is reported, or whether it is reported at
//!   all. [`Settings::severity`] answers for one diagnostic.
//! * **Code style**: `csharp_style_var_*`, `csharp_style_expression_bodied_*`,
//!   `dotnet_style_qualification_for_*`, `dotnet_sort_system_directives_first`,
//!   `csharp_using_directive_placement` and `csharp_style_namespace_declarations`
//!   are preferences the analyzers and refactorings consult, through
//!   [`CodeStyle`].
//! * **Naming**: `dotnet_naming_rule.*`, `dotnet_naming_symbols.*` and
//!   `dotnet_naming_style.*`, which the naming analyzer reads as they are.
//!
//! Each `.editorconfig` is parsed once and kept, keyed by its path and
//! checked against its [`Stamp`] before every use, as everything else in
//! the crate is: an edit to the file is seen at the next question without
//! anything having to say it changed.

use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};

use rustlyn_diagnostics::Severity;

use crate::fingerprint::Stamp;
use crate::format::{BraceNewLines, FormatOptions, SpaceAroundOperators};

// MARK: - one file

/// One `.editorconfig`, parsed.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EditorConfigFile {
    /// `root = true` before the first section: nothing above it is read.
    pub root: bool,
    pub sections: Vec<Section>,
}

/// A `[glob]` and the settings under it, keys lowercased, in order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Section {
    pub glob: String,
    pub properties: Vec<(String, String)>,
}

/// Parses the text of an `.editorconfig`. Lines that are not a section
/// header, a `key = value` pair, a comment or blank are skipped, as every
/// editorconfig reader does: a typo in one line costs that line only.
#[must_use]
pub fn parse(text: &str) -> EditorConfigFile {
    let mut file = EditorConfigFile::default();
    for raw in text.lines() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') || line.starts_with(';') {
            continue;
        }
        if let Some(header) = line.strip_prefix('[') {
            if let Some(glob) = header.strip_suffix(']') {
                file.sections.push(Section {
                    glob: glob.to_owned(),
                    properties: Vec::new(),
                });
            }
            continue;
        }
        // `=` separates when there is one; `:` also appears in values
        // (`true:warning`), so it separates only a line without `=`, as the
        // older form of the specification allowed.
        let Some((key, value)) = line.split_once('=').or_else(|| line.split_once(':')) else {
            continue;
        };
        let key = key.trim().to_ascii_lowercase();
        let value = value.trim().to_owned();
        if key.is_empty() {
            continue;
        }
        match file.sections.last_mut() {
            Some(section) => section.properties.push((key, value)),
            None => {
                if key == "root" {
                    file.root = value.eq_ignore_ascii_case("true");
                }
            }
        }
    }
    file
}

// MARK: - globs

/// Whether `path`, relative to the directory of the `.editorconfig` and
/// with `/` between its parts, matches a section's glob.
///
/// A glob without a `/` matches a file of that name in any directory below;
/// one with a `/` is anchored at the `.editorconfig`'s directory. `*` is any
/// run of characters but `/`, `**` any run at all, `?` one character, `[ab]`
/// and `[!ab]` a class, `{a,b}` either alternative, and `{1..9}` a number in
/// the range.
#[must_use]
pub fn glob_matches(glob: &str, path: &str) -> bool {
    let glob = glob.trim();
    let anchored = glob.contains('/');
    let glob = glob.strip_prefix('/').unwrap_or(glob);
    let full = if anchored {
        glob.to_owned()
    } else {
        format!("**/{glob}")
    };
    let path = path.trim_start_matches('/');
    expand_braces(&full)
        .iter()
        .any(|alternative| matches_pattern(&tokens(alternative), path.as_bytes()))
}

/// One piece of a glob with its braces expanded.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Piece {
    Literal(u8),
    /// `*`: anything but `/`.
    Star,
    /// `**`: anything. As `**/` it also matches no directory at all.
    Globstar,
    Any,
    Class {
        negated: bool,
        items: Vec<(u8, u8)>,
    },
    Number(i64, i64),
}

/// `{a,b}x` as `ax` and `bx`, nested braces too. `{1..3}` is left for the
/// matcher, as it stands for a number rather than a list.
fn expand_braces(glob: &str) -> Vec<String> {
    let bytes = glob.as_bytes();
    let mut depth = 0usize;
    let mut open = None;
    let mut escaped = false;
    for (index, &byte) in bytes.iter().enumerate() {
        if escaped {
            escaped = false;
            continue;
        }
        match byte {
            b'\\' => escaped = true,
            b'{' => {
                if depth == 0 {
                    open = Some(index);
                }
                depth += 1;
            }
            b'}' if depth > 0 => {
                depth -= 1;
                if depth == 0
                    && let Some(start) = open
                {
                    let inner = &glob[start + 1..index];
                    if is_number_range(inner) {
                        // Kept as it is; the rest may still have braces.
                        let rest = expand_braces(&glob[index + 1..]);
                        return rest
                            .into_iter()
                            .map(|tail| format!("{}{tail}", &glob[..=index]))
                            .collect();
                    }
                    let alternatives = split_top_level(inner);
                    if alternatives.len() < 2 {
                        // `{single}` is a literal in editorconfig.
                        let literal = format!("\\{{{inner}\\}}");
                        return expand_braces(&glob[index + 1..])
                            .into_iter()
                            .map(|tail| format!("{}{literal}{tail}", &glob[..start]))
                            .collect();
                    }
                    let mut found = Vec::new();
                    for alternative in alternatives {
                        let joined =
                            format!("{}{alternative}{}", &glob[..start], &glob[index + 1..]);
                        found.extend(expand_braces(&joined));
                    }
                    return found;
                }
            }
            _ => {}
        }
    }
    vec![glob.to_owned()]
}

fn split_top_level(inner: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut start = 0;
    for (index, byte) in inner.bytes().enumerate() {
        match byte {
            b'{' => depth += 1,
            b'}' => depth = depth.saturating_sub(1),
            b',' if depth == 0 => {
                parts.push(&inner[start..index]);
                start = index + 1;
            }
            _ => {}
        }
    }
    parts.push(&inner[start..]);
    parts
}

fn is_number_range(inner: &str) -> bool {
    number_range(inner).is_some()
}

fn number_range(inner: &str) -> Option<(i64, i64)> {
    let (from, to) = inner.split_once("..")?;
    Some((from.parse().ok()?, to.parse().ok()?))
}

fn tokens(glob: &str) -> Vec<Piece> {
    let bytes = glob.as_bytes();
    let mut pieces = Vec::new();
    let mut index = 0;
    while index < bytes.len() {
        let byte = bytes[index];
        match byte {
            b'\\' if index + 1 < bytes.len() => {
                pieces.push(Piece::Literal(bytes[index + 1]));
                index += 2;
                continue;
            }
            b'*' => {
                if bytes.get(index + 1) == Some(&b'*') {
                    pieces.push(Piece::Globstar);
                    index += 2;
                } else {
                    pieces.push(Piece::Star);
                    index += 1;
                }
                continue;
            }
            b'?' => pieces.push(Piece::Any),
            b'[' => {
                if let Some(close) = glob[index + 1..].find(']').map(|at| at + index + 1)
                    && close > index + 1
                {
                    let mut inner = &bytes[index + 1..close];
                    let negated = matches!(inner.first(), Some(b'!' | b'^'));
                    if negated {
                        inner = &inner[1..];
                    }
                    let mut items = Vec::new();
                    let mut at = 0;
                    while at < inner.len() {
                        if at + 2 < inner.len() && inner[at + 1] == b'-' {
                            items.push((inner[at], inner[at + 2]));
                            at += 3;
                        } else {
                            items.push((inner[at], inner[at]));
                            at += 1;
                        }
                    }
                    pieces.push(Piece::Class { negated, items });
                    index = close + 1;
                    continue;
                }
                pieces.push(Piece::Literal(b'['));
            }
            b'{' => {
                if let Some(close) = glob[index + 1..].find('}').map(|at| at + index + 1)
                    && let Some((from, to)) = number_range(&glob[index + 1..close])
                {
                    pieces.push(Piece::Number(from.min(to), from.max(to)));
                    index = close + 1;
                    continue;
                }
                pieces.push(Piece::Literal(b'{'));
            }
            _ => pieces.push(Piece::Literal(byte)),
        }
        index += 1;
    }
    pieces
}

/// Backtracking match of the pieces against the whole of `path`.
fn matches_pattern(pieces: &[Piece], path: &[u8]) -> bool {
    let Some((first, rest)) = pieces.split_first() else {
        return path.is_empty();
    };
    match first {
        Piece::Literal(byte) => path.first() == Some(byte) && matches_pattern(rest, &path[1..]),
        Piece::Any => path.first().is_some_and(|&c| c != b'/') && matches_pattern(rest, &path[1..]),
        Piece::Class { negated, items } => path.first().is_some_and(|&c| {
            c != b'/'
                && items.iter().any(|&(low, high)| (low..=high).contains(&c)) != *negated
                && matches_pattern(rest, &path[1..])
        }),
        Piece::Star => {
            for split in 0..=path.len() {
                if matches_pattern(rest, &path[split..]) {
                    return true;
                }
                if path.get(split) == Some(&b'/') {
                    break;
                }
            }
            false
        }
        Piece::Globstar => {
            // `**/` also matches nothing: `**/x.cs` matches `x.cs`.
            if let Some((Piece::Literal(b'/'), after)) = rest.split_first()
                && matches_pattern(after, path)
            {
                return true;
            }
            (0..=path.len()).any(|split| matches_pattern(rest, &path[split..]))
        }
        Piece::Number(from, to) => {
            let digits = path
                .iter()
                .enumerate()
                .take_while(|(index, c)| c.is_ascii_digit() || (*index == 0 && **c == b'-'))
                .count();
            (1..=digits).any(|length| {
                std::str::from_utf8(&path[..length])
                    .ok()
                    .and_then(|number| number.parse::<i64>().ok())
                    .is_some_and(|number| (*from..=*to).contains(&number))
                    && matches_pattern(rest, &path[length..])
            })
        }
    }
}

// MARK: - the settings of a file

/// What every `.editorconfig` above a file says about it, nearer files and
/// later sections winning. Keys are lowercased.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Settings {
    values: BTreeMap<String, String>,
}

/// How a diagnostic's severity is configured.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Configured {
    /// Nothing says: the analyzer's own default stands.
    Default,
    /// `none`: not reported at all.
    Suppressed,
    /// Reported at this severity. `silent` is hidden.
    At(Severity),
}

impl Settings {
    /// Settings from explicit pairs, as a test or an embedder has them.
    #[must_use]
    pub fn from_pairs<K: AsRef<str>, V: AsRef<str>>(
        pairs: impl IntoIterator<Item = (K, V)>,
    ) -> Self {
        Self {
            values: pairs
                .into_iter()
                .map(|(key, value)| {
                    (
                        key.as_ref().trim().to_ascii_lowercase(),
                        value.as_ref().trim().to_owned(),
                    )
                })
                .collect(),
        }
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// The value of `key` as written, if anything sets it.
    #[must_use]
    pub fn get(&self, key: &str) -> Option<&str> {
        self.values
            .get(&key.to_ascii_lowercase())
            .map(String::as_str)
    }

    /// Every key and its value, keys sorted.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &str)> {
        self.values
            .iter()
            .map(|(key, value)| (key.as_str(), value.as_str()))
    }

    /// The value of `key` without a `:severity` suffix, lowercased.
    #[must_use]
    pub fn value(&self, key: &str) -> Option<String> {
        self.get(key).map(|value| {
            value
                .split_once(':')
                .map_or(value, |(value, _)| value)
                .trim()
                .to_ascii_lowercase()
        })
    }

    /// `true` or `false`, as `key` says.
    #[must_use]
    pub fn flag(&self, key: &str) -> Option<bool> {
        match self.value(key)?.as_str() {
            "true" => Some(true),
            "false" => Some(false),
            _ => None,
        }
    }

    /// The `:severity` written after a code-style option's value, the older
    /// way of giving its diagnostic a severity.
    #[must_use]
    pub fn option_severity(&self, key: &str) -> Configured {
        self.get(key)
            .and_then(|value| value.split_once(':'))
            .map_or(Configured::Default, |(_, severity)| {
                parse_severity(severity).unwrap_or(Configured::Default)
            })
    }

    /// How diagnostic `id` is configured: its own
    /// `dotnet_diagnostic.<id>.severity`, then — for an analyzer's
    /// diagnostic, not the compiler's — its category's and then every
    /// analyzer's. An error the compiler reports cannot be turned down.
    #[must_use]
    pub fn severity(&self, id: &str, compiler_error: bool) -> Configured {
        if compiler_error {
            return Configured::Default;
        }
        let own = format!("dotnet_diagnostic.{}.severity", id.to_ascii_lowercase());
        if let Some(found) = self.get(&own).and_then(parse_severity) {
            return found;
        }
        if id.starts_with("CS") {
            return Configured::Default;
        }
        // Roslyn files every IDE diagnostic under the `Style` category.
        if id.starts_with("IDE")
            && let Some(found) = self
                .get("dotnet_analyzer_diagnostic.category-style.severity")
                .and_then(parse_severity)
        {
            return found;
        }
        self.get("dotnet_analyzer_diagnostic.severity")
            .and_then(parse_severity)
            .unwrap_or(Configured::Default)
    }

    /// `severity` for a diagnostic that also has a code-style option whose
    /// `:severity` suffix may say how loud it is.
    #[must_use]
    pub fn severity_with_option(&self, id: &str, option: &str) -> Configured {
        match self.severity(id, false) {
            Configured::Default => self.option_severity(option),
            found => found,
        }
    }

    /// The code-style preferences.
    #[must_use]
    pub fn code_style(&self) -> CodeStyle {
        CodeStyle::from_settings(self)
    }

    /// `base` with whatever these settings say about layout on top.
    #[must_use]
    pub fn format_options(&self, mut base: FormatOptions) -> FormatOptions {
        match self.value("indent_style").as_deref() {
            Some("tab") => base.use_tabs = true,
            Some("space") => base.use_tabs = false,
            _ => {}
        }
        let tab_width = self.value("tab_width").and_then(|value| value.parse().ok());
        match self.value("indent_size").as_deref() {
            Some("tab") => {
                if let Some(width) = tab_width {
                    base.indent_size = width;
                }
            }
            Some(size) => {
                if let Ok(size) = size.parse::<u32>()
                    && size > 0
                {
                    base.indent_size = size;
                    // The specification: `tab_width` defaults to
                    // `indent_size` when that is a number.
                    if tab_width.is_none() {
                        base.tab_size = size;
                    }
                }
            }
            None => {}
        }
        if let Some(width) = tab_width.filter(|&width: &u32| width > 0) {
            base.tab_size = width;
        }
        match self.value("end_of_line").as_deref() {
            Some("lf") => "\n".clone_into(&mut base.newline),
            Some("crlf") => "\r\n".clone_into(&mut base.newline),
            Some("cr") => "\r".clone_into(&mut base.newline),
            _ => {}
        }
        if let Some(value) = self.flag("insert_final_newline") {
            base.insert_final_newline = Some(value);
        }
        let style = &mut base.style;
        if let Some(value) = self.value("csharp_new_line_before_open_brace") {
            style.new_line_before_open_brace = BraceNewLines::parse(&value);
        }
        let flags: [(&str, &mut bool); 14] = [
            (
                "csharp_new_line_before_else",
                &mut style.new_line_before_else,
            ),
            (
                "csharp_new_line_before_catch",
                &mut style.new_line_before_catch,
            ),
            (
                "csharp_new_line_before_finally",
                &mut style.new_line_before_finally,
            ),
            (
                "csharp_indent_case_contents",
                &mut style.indent_case_contents,
            ),
            (
                "csharp_indent_switch_labels",
                &mut style.indent_switch_labels,
            ),
            ("csharp_space_after_cast", &mut style.space_after_cast),
            (
                "csharp_space_after_keywords_in_control_flow_statements",
                &mut style.space_after_control_flow_keywords,
            ),
            (
                "csharp_space_between_method_call_parameter_list_parentheses",
                &mut style.space_within_call_parentheses,
            ),
            (
                "csharp_space_between_method_declaration_parameter_list_parentheses",
                &mut style.space_within_declaration_parentheses,
            ),
            (
                "csharp_space_between_method_call_name_and_opening_parenthesis",
                &mut style.space_before_call_parenthesis,
            ),
            (
                "csharp_space_between_method_declaration_name_and_open_parenthesis",
                &mut style.space_before_declaration_parenthesis,
            ),
            ("csharp_space_after_comma", &mut style.space_after_comma),
            (
                "csharp_preserve_single_line_statements",
                &mut style.preserve_single_line_statements,
            ),
            (
                "csharp_preserve_single_line_blocks",
                &mut style.preserve_single_line_blocks,
            ),
        ];
        for (key, slot) in flags {
            if let Some(value) = self.flag(key) {
                *slot = value;
            }
        }
        if let Some(value) = self.flag("csharp_space_before_colon_in_inheritance_clause") {
            style.space_before_inheritance_colon = value;
        }
        if let Some(value) = self.flag("csharp_space_after_colon_in_inheritance_clause") {
            style.space_after_inheritance_colon = value;
        }
        match self
            .value("csharp_space_around_binary_operators")
            .as_deref()
        {
            Some("before_and_after") => {
                style.space_around_binary_operators = SpaceAroundOperators::BeforeAndAfter;
            }
            Some("none") => style.space_around_binary_operators = SpaceAroundOperators::None,
            Some("ignore") => style.space_around_binary_operators = SpaceAroundOperators::Ignore,
            _ => {}
        }
        base
    }
}

/// `none`, `silent`, `suggestion`, `warning`, `error`, or `default`.
fn parse_severity(text: &str) -> Option<Configured> {
    Some(match text.trim().to_ascii_lowercase().as_str() {
        "none" => Configured::Suppressed,
        "silent" | "refactoring" | "hidden" => Configured::At(Severity::Hidden),
        "suggestion" | "info" => Configured::At(Severity::Info),
        "warning" | "warn" => Configured::At(Severity::Warning),
        "error" => Configured::At(Severity::Error),
        "default" => Configured::Default,
        _ => return None,
    })
}

// MARK: - code style

/// When `var` is preferred, for one of Roslyn's three cases.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct VarPreference {
    /// `csharp_style_var_for_built_in_types`: `int`, `string`.
    pub built_in: Option<bool>,
    /// `csharp_style_var_when_type_is_apparent`: `new Foo()`, a cast.
    pub apparent: Option<bool>,
    /// `csharp_style_var_elsewhere`.
    pub elsewhere: Option<bool>,
}

/// Where an expression body is preferred: `true`, `false` or `when_on_single_line`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExpressionBodyPreference {
    Never,
    Always,
    WhenOnSingleLine,
}

/// Where `using` directives go: `outside_namespace` or `inside_namespace`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UsingPlacement {
    OutsideNamespace,
    InsideNamespace,
}

/// The code-style options the analyzers and refactorings consult. `None`
/// where the settings say nothing, and Roslyn's default applies.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CodeStyle {
    pub var: VarPreference,
    /// By Roslyn's option suffix: `methods`, `constructors`, `operators`,
    /// `conversion_operators`, `properties`, `indexers`, `accessors`,
    /// `lambdas`, `local_functions`.
    pub expression_bodied: BTreeMap<String, ExpressionBodyPreference>,
    /// `dotnet_sort_system_directives_first`.
    pub system_directives_first: Option<bool>,
    /// `dotnet_separate_import_directive_groups`.
    pub separate_import_groups: Option<bool>,
    pub using_placement: Option<UsingPlacement>,
    /// `csharp_style_namespace_declarations`: `Some(true)` for
    /// `file_scoped`.
    pub file_scoped_namespaces: Option<bool>,
    /// `dotnet_style_qualification_for_{field,property,method,event}`.
    pub qualify_field: Option<bool>,
    pub qualify_property: Option<bool>,
    pub qualify_method: Option<bool>,
    pub qualify_event: Option<bool>,
    /// `dotnet_style_predefined_type_for_member_access` and
    /// `..._for_locals_parameters_members`.
    pub predefined_type_for_member_access: Option<bool>,
    pub predefined_type_for_declarations: Option<bool>,
}

/// The suffixes of `csharp_style_expression_bodied_*`.
pub const EXPRESSION_BODIED_KINDS: &[&str] = &[
    "methods",
    "constructors",
    "operators",
    "conversion_operators",
    "properties",
    "indexers",
    "accessors",
    "lambdas",
    "local_functions",
];

impl CodeStyle {
    fn from_settings(settings: &Settings) -> Self {
        let mut expression_bodied = BTreeMap::new();
        for kind in EXPRESSION_BODIED_KINDS {
            let key = format!("csharp_style_expression_bodied_{kind}");
            let preference = match settings.value(&key).as_deref() {
                Some("true") => ExpressionBodyPreference::Always,
                Some("false") => ExpressionBodyPreference::Never,
                Some("when_on_single_line") => ExpressionBodyPreference::WhenOnSingleLine,
                _ => continue,
            };
            expression_bodied.insert((*kind).to_owned(), preference);
        }
        Self {
            var: VarPreference {
                built_in: settings.flag("csharp_style_var_for_built_in_types"),
                apparent: settings.flag("csharp_style_var_when_type_is_apparent"),
                elsewhere: settings.flag("csharp_style_var_elsewhere"),
            },
            expression_bodied,
            system_directives_first: settings.flag("dotnet_sort_system_directives_first"),
            separate_import_groups: settings.flag("dotnet_separate_import_directive_groups"),
            using_placement: match settings
                .value("csharp_using_directive_placement")
                .as_deref()
            {
                Some("outside_namespace") => Some(UsingPlacement::OutsideNamespace),
                Some("inside_namespace") => Some(UsingPlacement::InsideNamespace),
                _ => None,
            },
            file_scoped_namespaces: match settings
                .value("csharp_style_namespace_declarations")
                .as_deref()
            {
                Some("file_scoped") => Some(true),
                Some("block_scoped") => Some(false),
                _ => None,
            },
            qualify_field: settings.flag("dotnet_style_qualification_for_field"),
            qualify_property: settings.flag("dotnet_style_qualification_for_property"),
            qualify_method: settings.flag("dotnet_style_qualification_for_method"),
            qualify_event: settings.flag("dotnet_style_qualification_for_event"),
            predefined_type_for_member_access: settings
                .flag("dotnet_style_predefined_type_for_member_access"),
            predefined_type_for_declarations: settings
                .flag("dotnet_style_predefined_type_for_locals_parameters_members"),
        }
    }

    /// The expression-body preference for one kind of declaration.
    #[must_use]
    pub fn expression_body(&self, kind: &str) -> Option<ExpressionBodyPreference> {
        self.expression_bodied.get(kind).copied()
    }
}

// MARK: - the style code is being written in

thread_local! {
    /// The code style of the file the light bulb is working on, for the
    /// helpers deep inside the providers — the one that places a `using`,
    /// the one that writes a namespace — which are handed a tree and a text
    /// but not the settings.
    static STYLE: std::cell::RefCell<Option<CodeStyle>> = const { std::cell::RefCell::new(None) };
}

/// Runs `body` with `style` as the code style that
/// [`current_code_style`] answers, and puts back whatever was there.
pub fn with_code_style<T>(style: CodeStyle, body: impl FnOnce() -> T) -> T {
    let previous = STYLE.with(|slot| slot.replace(Some(style)));
    struct Restore(Option<CodeStyle>);
    impl Drop for Restore {
        fn drop(&mut self) {
            let previous = self.0.take();
            STYLE.with(|slot| *slot.borrow_mut() = previous);
        }
    }
    let _restore = Restore(previous);
    body()
}

/// The code style the current light-bulb question runs under: Roslyn's
/// defaults outside [`with_code_style`].
#[must_use]
pub fn current_code_style() -> CodeStyle {
    STYLE.with(|slot| slot.borrow().clone().unwrap_or_default())
}

/// The code style a caller set with [`with_code_style`], if one did.
#[must_use]
pub fn ambient_code_style() -> Option<CodeStyle> {
    STYLE.with(|slot| slot.borrow().clone())
}

/// How a namespace sorts among `using`s: `System` and its children first
/// unless `dotnet_sort_system_directives_first` says otherwise.
#[must_use]
pub fn using_sort_key(name: &str) -> (bool, String) {
    let system_first = current_code_style().system_directives_first.unwrap_or(true);
    let system = name == "System" || name.starts_with("System.");
    (system_first && !system, name.to_ascii_lowercase())
}

// MARK: - finding and caching the files

/// A parsed `.editorconfig` and the stamp it was read under.
type Kept = (Stamp, Arc<EditorConfigFile>);

fn kept() -> &'static Mutex<HashMap<PathBuf, Kept>> {
    static KEPT: OnceLock<Mutex<HashMap<PathBuf, Kept>>> = OnceLock::new();
    KEPT.get_or_init(|| Mutex::new(HashMap::new()))
}

/// The `.editorconfig` at `path`, parsed, from the cache while its stamp
/// still matches; `None` when there is none.
fn load(path: &Path) -> Option<Arc<EditorConfigFile>> {
    let stamp = Stamp::of(path)?;
    if !std::fs::metadata(path).is_ok_and(|metadata| metadata.is_file()) {
        return None;
    }
    let mut cache = kept().lock().unwrap_or_else(|error| error.into_inner());
    if let Some((was, file)) = cache.get(path)
        && stamp.matches(*was)
    {
        return Some(file.clone());
    }
    let text = std::fs::read_to_string(path).ok()?;
    let file = Arc::new(parse(&text));
    cache.insert(path.to_path_buf(), (stamp, file.clone()));
    Some(file)
}

/// The settings for the file at `path`: every `.editorconfig` from its
/// directory up to a `root = true` one, applied from the top down.
#[must_use]
pub fn settings_for(path: &Path) -> Settings {
    let mut found: Vec<(PathBuf, Arc<EditorConfigFile>)> = Vec::new();
    let mut directory = path.parent();
    while let Some(dir) = directory {
        let candidate = dir.join(".editorconfig");
        if let Some(file) = load(&candidate) {
            let root = file.root;
            found.push((dir.to_path_buf(), file));
            if root {
                break;
            }
        }
        directory = dir.parent();
    }
    let mut values = BTreeMap::new();
    for (dir, file) in found.iter().rev() {
        let relative = path.strip_prefix(dir).unwrap_or(path);
        let relative = relative
            .components()
            .map(|part| part.as_os_str().to_string_lossy())
            .collect::<Vec<_>>()
            .join("/");
        apply_file(file, &relative, &mut values);
    }
    Settings { values }
}

/// Applies the sections of one file that match `relative`, in order.
fn apply_file(file: &EditorConfigFile, relative: &str, values: &mut BTreeMap<String, String>) {
    for section in &file.sections {
        if glob_matches(&section.glob, relative) {
            for (key, value) in &section.properties {
                // `unset` removes what a farther file said.
                if value.eq_ignore_ascii_case("unset") {
                    values.remove(key);
                } else {
                    values.insert(key.clone(), value.clone());
                }
            }
        }
    }
}

/// The settings `text` would give `relative`, as though it were the only
/// `.editorconfig`: for tests, and for an editor previewing one.
#[must_use]
pub fn settings_from_text(text: &str, relative: &str) -> Settings {
    let mut values = BTreeMap::new();
    apply_file(&parse(text), relative, &mut values);
    Settings { values }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn globs_match_the_way_the_specification_says() {
        assert!(glob_matches("*.cs", "A.cs"));
        assert!(glob_matches("*.cs", "src/deep/A.cs"));
        assert!(!glob_matches("*.cs", "A.csx"));
        assert!(glob_matches("*.{cs,csx}", "src/A.csx"));
        assert!(glob_matches("{*.cs,*.vb}", "B.vb"));
        assert!(glob_matches("src/*.cs", "src/A.cs"));
        assert!(!glob_matches("src/*.cs", "src/x/A.cs"));
        assert!(!glob_matches("src/*.cs", "other/src/A.cs"));
        assert!(glob_matches("src/**/*.cs", "src/x/y/A.cs"));
        assert!(glob_matches("src/**/*.cs", "src/A.cs"));
        assert!(glob_matches("/src/*.cs", "src/A.cs"));
        assert!(glob_matches("**/Tests/*.cs", "a/b/Tests/T.cs"));
        assert!(glob_matches("*", "anything/at/all.txt"));
        assert!(glob_matches("[Ff]oo.cs", "foo.cs"));
        assert!(!glob_matches("[!F]oo.cs", "Foo.cs"));
        assert!(glob_matches("file?.cs", "file1.cs"));
        assert!(glob_matches("file{1..3}.cs", "file2.cs"));
        assert!(!glob_matches("file{1..3}.cs", "file4.cs"));
        assert!(glob_matches("{src,test}/**/{*.cs,*.csx}", "test/a/b.csx"));
    }

    #[test]
    fn a_file_parses_into_sections() {
        let file = parse(
            "# comment\nroot = true\n\n[*]\nindent_style = space\n; another\n[*.cs]\nIndent_Size = 2\ncsharp_style_var_elsewhere = true:warning\nnot a pair\n",
        );
        assert!(file.root);
        assert_eq!(file.sections.len(), 2);
        assert_eq!(
            file.sections[1].properties,
            vec![
                ("indent_size".to_string(), "2".to_string()),
                (
                    "csharp_style_var_elsewhere".to_string(),
                    "true:warning".to_string()
                )
            ]
        );
    }

    #[test]
    fn later_sections_win_and_values_carry_severities() {
        let settings = settings_from_text(
            "[*]\nindent_size = 4\n[*.cs]\nindent_size = 2\ncsharp_style_var_elsewhere = true:warning\ndotnet_diagnostic.IDE0051.severity = none\ndotnet_analyzer_diagnostic.severity = warning\n",
            "src/A.cs",
        );
        assert_eq!(settings.get("indent_size"), Some("2"));
        assert_eq!(settings.flag("csharp_style_var_elsewhere"), Some(true));
        assert_eq!(
            settings.option_severity("csharp_style_var_elsewhere"),
            Configured::At(Severity::Warning)
        );
        assert_eq!(settings.severity("IDE0051", false), Configured::Suppressed);
        assert_eq!(
            settings.severity("IDE0059", false),
            Configured::At(Severity::Warning)
        );
        // The compiler's own diagnostics are not an analyzer's.
        assert_eq!(settings.severity("CS0168", false), Configured::Default);
        assert_eq!(settings.severity("CS0103", true), Configured::Default);
    }

    #[test]
    fn layout_settings_become_format_options() {
        let settings = settings_from_text(
            "[*.cs]\nindent_style = tab\nindent_size = 2\nend_of_line = crlf\ninsert_final_newline = true\ncsharp_new_line_before_open_brace = methods, types\ncsharp_new_line_before_else = false\ncsharp_space_after_cast = true\n",
            "A.cs",
        );
        let options = settings.format_options(FormatOptions::default());
        assert!(options.use_tabs);
        assert_eq!((options.indent_size, options.tab_size), (2, 2));
        assert_eq!(options.newline, "\r\n");
        assert_eq!(options.insert_final_newline, Some(true));
        assert!(options.style.new_line_before_open_brace.methods);
        assert!(options.style.new_line_before_open_brace.types);
        assert!(!options.style.new_line_before_open_brace.control_blocks);
        assert!(!options.style.new_line_before_else);
        assert!(options.style.space_after_cast);
    }

    #[test]
    fn nearer_files_override_and_root_stops_the_walk() {
        let base = std::env::temp_dir().join(format!(
            "rustlyn-editorconfig-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let deep = base.join("repo/src/game");
        std::fs::create_dir_all(&deep).unwrap();
        std::fs::write(base.join(".editorconfig"), "[*]\nfar_away = yes\n").unwrap();
        std::fs::write(
            base.join("repo/.editorconfig"),
            "root = true\n[*.cs]\nindent_size = 4\ncsharp_style_var_elsewhere = false\n",
        )
        .unwrap();
        std::fs::write(
            base.join("repo/src/.editorconfig"),
            "[game/*.cs]\nindent_size = 2\n[*.txt]\nindent_size = 8\n",
        )
        .unwrap();
        let settings = settings_for(&deep.join("Pawn.cs"));
        assert_eq!(settings.get("indent_size"), Some("2"));
        assert_eq!(settings.get("csharp_style_var_elsewhere"), Some("false"));
        assert_eq!(settings.get("far_away"), None);

        // A change to a file is seen at the next question.
        std::fs::write(
            base.join("repo/src/.editorconfig"),
            "[game/*.cs]\nindent_size = 3\nextra = 1\n",
        )
        .unwrap();
        let settings = settings_for(&deep.join("Pawn.cs"));
        assert_eq!(settings.get("indent_size"), Some("3"));
        std::fs::remove_dir_all(&base).ok();
    }

    #[test]
    fn code_style_reads_roslyns_options() {
        let settings = settings_from_text(
            "[*.cs]\ncsharp_style_var_for_built_in_types = true:suggestion\ncsharp_style_var_when_type_is_apparent = true\ncsharp_style_var_elsewhere = false\ncsharp_style_expression_bodied_methods = when_on_single_line\ncsharp_style_expression_bodied_properties = true\ncsharp_style_namespace_declarations = file_scoped:warning\ndotnet_style_qualification_for_field = true\ndotnet_sort_system_directives_first = false\ncsharp_using_directive_placement = inside_namespace\n",
            "A.cs",
        );
        let style = settings.code_style();
        assert_eq!(style.var.built_in, Some(true));
        assert_eq!(style.var.apparent, Some(true));
        assert_eq!(style.var.elsewhere, Some(false));
        assert_eq!(
            style.expression_body("methods"),
            Some(ExpressionBodyPreference::WhenOnSingleLine)
        );
        assert_eq!(
            style.expression_body("properties"),
            Some(ExpressionBodyPreference::Always)
        );
        assert_eq!(style.file_scoped_namespaces, Some(true));
        assert_eq!(style.qualify_field, Some(true));
        assert_eq!(style.system_directives_first, Some(false));
        assert_eq!(style.using_placement, Some(UsingPlacement::InsideNamespace));
    }
}
