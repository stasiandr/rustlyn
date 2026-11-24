//! The editor-facing side of Rustlyn.
//!
//! A compiler and an editor want different things from the same code. A
//! compiler is asked one question, about all of the code, and may take as
//! long as the answer needs. An editor is asked a question a frame, about
//! whatever is on screen, and has sixteen milliseconds. The same analysis
//! serves both only if it can be stopped early, started in the middle and
//! reused from last time — and that is what this crate is: the layers of
//! rustlyn arranged so that each one answers before the one above it has
//! begun.
//!
//! The layers, in the order an editor needs them:
//!
//! 1. **[Open](document).** Bytes into text. No parsing, no lexing — the
//!    file is on screen before anything has been decided about it.
//! 2. **[Colour](highlight).** The lexer, over the lines that are visible and
//!    no others, resumed from a checkpoint rather than started at the top.
//! 3. **[Outline](outline).** The parser, over this one file: what it
//!    declares, and what those declarations say. This is where the real
//!    grammar replaces guessing at shapes.
//! 4. **[Index](index).** The same, over the whole project, so a name can be
//!    followed to where it was declared.
//! 5. **[Decompile](decompile).** Assemblies with no source: their surface
//!    from the metadata, and a method's body from its IL when asked for one.
//!
//! Every layer is a pure function of a file's bytes, so every layer is
//! [cached](cache) the same way, and the check that comes before any work is
//! always the same question: have the inputs changed? A stamp answers it
//! without reading, a hash answers it without recomputing, and only a real
//! change gets as far as doing the work again.
//!
//! Everything above layer 1 is about C#. An editor opens more than C#, and
//! [`Document::is_csharp`] is the gate: a file that is not C# is still a
//! document, it just gets nothing from the layers above.

pub mod cache;
pub mod decompile;
pub mod document;
pub mod edit;
pub mod fingerprint;
pub mod formats;
pub mod highlight;
pub mod hot;
pub mod index;
pub mod navigate;
pub mod outline;
pub mod project;
pub mod search;
pub mod selection;
pub mod semantic;
pub mod session;
pub mod utf16;
pub mod wire;

// MARK: - syntax-level editing: formatting, structure, braces, comments
pub mod braces;
pub mod comment;
pub mod doc_comment;
pub mod format;
pub mod structure;

// MARK: - .editorconfig: layout, severities, code style and naming
pub mod editorconfig;

pub use cache::{Cache, Key, Layer, Lookup, Statistics};
pub use decompile::{AssemblySurface, MethodBody};
pub use document::{Document, Encoding, Indent, LineEnding};
pub use edit::{FileEdit, TextEdit, WorkspaceEdit};
pub use fingerprint::{Fingerprint, Freshness, Stamp};
pub use highlight::{Class, Classified, Highlighter};
pub use index::{Confidence, Entry, Found, IndexedFile, ProjectIndex};
pub use navigate::{Miss, Target, definition_at};
pub use outline::{Declaration, DeclarationKind, FileOutline, Parameter, PassedBy, Using};
pub use session::{Definition, Location, Refusal, Run, Session};
pub use utf16::Utf16Map;
