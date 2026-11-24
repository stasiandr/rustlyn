use std::fmt;

use rustlyn_text::{SourceText, TextSpan};

use crate::{ErrorCode, Severity};

/// A single compiler message anchored to a span of source text.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Diagnostic {
    code: ErrorCode,
    severity: Severity,
    span: TextSpan,
    message: String,
}

impl Diagnostic {
    /// Creates a diagnostic, formatting the code's message template with `args`.
    #[must_use]
    pub fn new(code: ErrorCode, span: TextSpan, args: &[&str]) -> Self {
        Self {
            code,
            severity: code.default_severity(),
            span,
            message: format_template(code.message_template(), args),
        }
    }

    /// Creates a diagnostic with no message arguments.
    #[must_use]
    pub fn simple(code: ErrorCode, span: TextSpan) -> Self {
        Self::new(code, span, &[])
    }

    /// Overrides the severity, as `#pragma warning` and `/warnaserror` do.
    #[must_use]
    pub fn with_severity(mut self, severity: Severity) -> Self {
        self.severity = severity;
        self
    }

    /// The same message somewhere else: the place a diagnostic was found in
    /// one version of a text, carried over to another.
    #[must_use]
    pub const fn with_span(mut self, span: TextSpan) -> Self {
        self.span = span;
        self
    }

    #[must_use]
    pub const fn code(&self) -> ErrorCode {
        self.code
    }

    #[must_use]
    pub const fn severity(&self) -> Severity {
        self.severity
    }

    #[must_use]
    pub const fn span(&self) -> TextSpan {
        self.span
    }

    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }

    #[must_use]
    pub fn is_error(&self) -> bool {
        self.severity == Severity::Error
    }

    /// Wraps the diagnostic so that `Display` includes the file and position,
    /// in the `file(line,col): error CSxxxx: message` shape `csc` uses.
    #[must_use]
    pub fn display_with<'a>(&'a self, source: &'a SourceText) -> DiagnosticDisplay<'a> {
        DiagnosticDisplay {
            diagnostic: self,
            source,
        }
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}: {}", self.severity, self.code, self.message)
    }
}

/// A [`Diagnostic`] paired with the text it points into; see
/// [`Diagnostic::display_with`].
#[derive(Debug)]
pub struct DiagnosticDisplay<'a> {
    diagnostic: &'a Diagnostic,
    source: &'a SourceText,
}

impl fmt::Display for DiagnosticDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let position = self.source.line_position(self.diagnostic.span.start());
        write!(
            f,
            "{}({},{}): {} {}: {}",
            self.source.name(),
            position.line + 1,
            position.character + 1,
            self.diagnostic.severity,
            self.diagnostic.code,
            self.diagnostic.message,
        )
    }
}

/// Collects diagnostics in the order they are reported.
#[derive(Clone, Default, Debug)]
pub struct DiagnosticBag {
    diagnostics: Vec<Diagnostic>,
}

impl DiagnosticBag {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            diagnostics: Vec::new(),
        }
    }

    pub fn report(&mut self, diagnostic: Diagnostic) {
        self.diagnostics.push(diagnostic);
    }

    /// Reports `code` at `span` with formatted arguments.
    pub fn error(&mut self, code: ErrorCode, span: TextSpan, args: &[&str]) {
        self.report(Diagnostic::new(code, span, args));
    }

    pub fn extend(&mut self, diagnostics: impl IntoIterator<Item = Diagnostic>) {
        self.diagnostics.extend(diagnostics);
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.diagnostics.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.diagnostics.is_empty()
    }

    #[must_use]
    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(Diagnostic::is_error)
    }

    #[must_use]
    pub fn as_slice(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    /// Drops everything reported after `len`.
    ///
    /// The parser uses this to undo a speculative attempt: when it backs out of
    /// reading `(x)` as a cast, the complaints it made along the way have to go
    /// too.
    pub fn truncate(&mut self, len: usize) {
        self.diagnostics.truncate(len);
    }

    /// Sorts by position, then by code, so output is stable across runs.
    pub fn sort(&mut self) {
        self.diagnostics
            .sort_by_key(|d| (d.span().start(), d.span().end(), d.code()));
    }

    #[must_use]
    pub fn into_vec(self) -> Vec<Diagnostic> {
        self.diagnostics
    }
}

impl IntoIterator for DiagnosticBag {
    type Item = Diagnostic;
    type IntoIter = std::vec::IntoIter<Diagnostic>;

    fn into_iter(self) -> Self::IntoIter {
        self.diagnostics.into_iter()
    }
}

impl<'a> IntoIterator for &'a DiagnosticBag {
    type Item = &'a Diagnostic;
    type IntoIter = std::slice::Iter<'a, Diagnostic>;

    fn into_iter(self) -> Self::IntoIter {
        self.diagnostics.iter()
    }
}

/// Substitutes `{0}`, `{1}`, ... in `template` with `args`.
///
/// Out-of-range placeholders and `{` that starts no placeholder are copied
/// through unchanged, so a malformed template degrades instead of panicking.
fn format_template(template: &str, args: &[&str]) -> String {
    if !template.contains('{') {
        return template.to_string();
    }

    let mut out = String::with_capacity(template.len());
    let mut rest = template;
    while let Some(open) = rest.find('{') {
        out.push_str(&rest[..open]);
        rest = &rest[open + 1..];
        match rest.find('}') {
            Some(close) => {
                let body = &rest[..close];
                match body.parse::<usize>() {
                    Ok(index) if index < args.len() => out.push_str(args[index]),
                    _ => {
                        out.push('{');
                        out.push_str(body);
                        out.push('}');
                    }
                }
                rest = &rest[close + 1..];
            }
            None => {
                out.push('{');
                break;
            }
        }
    }
    out.push_str(rest);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formats_arguments() {
        let diagnostic = Diagnostic::new(
            ErrorCode::ErrUnexpectedCharacter,
            TextSpan::new(4, 1),
            &["$"],
        );
        assert_eq!(diagnostic.message(), "Unexpected character '$'");
        assert_eq!(
            diagnostic.to_string(),
            "error CS1056: Unexpected character '$'"
        );
    }

    #[test]
    fn missing_arguments_are_left_alone() {
        assert_eq!(format_template("a {0} b {1}", &["x"]), "a x b {1}");
        assert_eq!(format_template("nothing", &[]), "nothing");
        assert_eq!(format_template("unclosed {", &[]), "unclosed {");
    }

    #[test]
    fn renders_a_position() {
        let source = SourceText::new("Program.cs", "class C\n{ $ }\n");
        let diagnostic = Diagnostic::new(
            ErrorCode::ErrUnexpectedCharacter,
            TextSpan::new(10, 1),
            &["$"],
        );
        assert_eq!(
            diagnostic.display_with(&source).to_string(),
            "Program.cs(2,3): error CS1056: Unexpected character '$'"
        );
    }

    #[test]
    fn bag_tracks_errors() {
        let mut bag = DiagnosticBag::new();
        assert!(bag.is_empty());
        bag.error(ErrorCode::ErrEmptyCharConst, TextSpan::new(2, 2), &[]);
        assert!(bag.has_errors());
        assert_eq!(bag.len(), 1);
    }
}
