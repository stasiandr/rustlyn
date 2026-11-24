// The C interface to Rustlyn's editor layers.
//
// Written by hand rather than generated, because it is read far more often
// than it changes and a generated header explains nothing. It must stay in
// step with `crates/rustlyn-ffi/src/lib.rs`: every struct here is `#[repr(C)]`
// there, and the two enums are mirrored by hand. `rln_declaration_kind_count`
// and `rln_class_count` exist so a caller can check at runtime that its own
// copies of those tables still line up with the library it linked against.
//
// The rules, in full:
//
//   * Every `const char *` in is NUL-terminated UTF-8. Null is refused with
//     RLN_BAD_ARGUMENT except where a comment says otherwise.
//   * Every result with a free function must be freed by it, exactly once.
//     Rust allocated it, so Rust has to release it; `free()` on one of these
//     is undefined behaviour that appears to work.
//   * A result's `strings` blob owns every string in it. The `RlnText` fields
//     are offsets into that blob, not pointers, and they are only valid until
//     the result is freed.
//   * A session may be used from as many threads as you like, at once. A
//     single result may not be freed from two.
//   * Offsets and lengths that describe places in a file are UTF-16 code
//     units, which is what NSRange and LSP count in. Lines are zero-based.

#ifndef RUSTLYN_H
#define RUSTLYN_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

// MARK: - status

typedef enum RlnStatus {
    RLN_OK = 0,
    /// The file is not open. Call rln_open first.
    RLN_NOT_OPEN = 1,
    /// The file is not C#. Layer 1 still works; nothing above it does.
    RLN_NOT_CSHARP = 2,
    /// The project has not been indexed. Call rln_reindex.
    RLN_NOT_INDEXED = 3,
    /// The cursor is not on a name.
    RLN_NOT_A_NAME = 4,
    /// The receiver of a member access could not be typed, so looking the
    /// name up on its own would be a guess. rln_last_error names the receiver.
    RLN_RECEIVER_UNKNOWN = 5,
    /// The name is not declared in this project — usually a type from an
    /// assembly, which is what the layer 5 calls are for.
    RLN_NOT_IN_PROJECT = 6,
    /// The assembly could not be read. rln_last_error says why.
    RLN_ASSEMBLY = 7,
    /// The file could not be read. rln_last_error says why.
    RLN_IO = 8,
    /// A pointer was null or a string was not UTF-8: a bug on this side.
    RLN_BAD_ARGUMENT = 9,
    /// Something inside the library panicked: a bug on that side. The session
    /// is still usable.
    RLN_PANICKED = 10,
    /// The project has not been compiled. Call rln_compile.
    RLN_NOT_COMPILED = 11,
    /// The caller called it off (rln_cancel_code_lens) before it finished.
    RLN_CANCELLED = 12
} RlnStatus;

/// What a declaration declares. Mirrors `DeclarationKind`; check the count
/// with rln_declaration_kind_count().
typedef enum RlnDeclarationKind {
    RLN_NAMESPACE = 0,
    RLN_CLASS = 1,
    RLN_STRUCT = 2,
    RLN_INTERFACE = 3,
    RLN_ENUM = 4,
    RLN_RECORD = 5,
    RLN_DELEGATE = 6,
    RLN_METHOD = 7,
    RLN_CONSTRUCTOR = 8,
    RLN_DESTRUCTOR = 9,
    RLN_PROPERTY = 10,
    RLN_INDEXER = 11,
    RLN_FIELD = 12,
    RLN_EVENT = 13,
    RLN_ENUM_MEMBER = 14,
    RLN_OPERATOR = 15,
    RLN_EXTENSION = 16
} RlnDeclarationKind;

/// What a run of text is, for colour. Mirrors `Class`; check the count with
/// rln_class_count().
typedef enum RlnClass {
    RLN_PLAIN = 0,
    RLN_KEYWORD = 1,
    RLN_TYPE = 2,
    RLN_STRING = 3,
    RLN_ESCAPE = 4,
    RLN_NUMBER = 5,
    RLN_COMMENT = 6,
    RLN_DOC_COMMENT = 7,
    RLN_FUNCTION = 8,
    RLN_PUNCTUATION = 9,
    RLN_PREPROCESSOR = 10,
    RLN_ATTRIBUTE = 11,
    RLN_CONSTANT = 12,
    RLN_OPERATOR_TOKEN = 13,
    /// Inside an #if whose condition was false: to be greyed, not coloured.
    RLN_DISABLED = 14
} RlnClass;

/// What a completion is, for its icon. Mirrors `CompletionKind`; check the
/// count with rln_completion_kind_count().
typedef enum RlnCompletionKind {
    RLN_COMPLETION_METHOD = 0,
    RLN_COMPLETION_FIELD = 1,
    RLN_COMPLETION_PROPERTY = 2,
    RLN_COMPLETION_EVENT = 3,
    RLN_COMPLETION_LOCAL = 4,
    RLN_COMPLETION_PARAMETER = 5,
    RLN_COMPLETION_CLASS = 6,
    RLN_COMPLETION_STRUCT = 7,
    RLN_COMPLETION_INTERFACE = 8,
    RLN_COMPLETION_ENUM = 9,
    RLN_COMPLETION_ENUM_MEMBER = 10,
    RLN_COMPLETION_DELEGATE = 11,
    RLN_COMPLETION_NAMESPACE = 12,
    RLN_COMPLETION_KEYWORD = 13,
    RLN_COMPLETION_TYPE_PARAMETER = 14,
    RLN_COMPLETION_CONSTANT = 15,
    /// A code snippet by its shortcut: `cw`, `prop`. Only rln_completions_ex
    /// returns these.
    RLN_COMPLETION_SNIPPET = 16
} RlnCompletionKind;

/// Bits in RlnDeclaration.flags.
enum {
    RLN_FLAG_STATIC = 1 << 0,
    RLN_FLAG_ABSTRACT = 1 << 1,
    RLN_FLAG_OVERRIDE = 1 << 2,
    RLN_FLAG_PARTIAL = 1 << 3,
    RLN_FLAG_EXTENSION_METHOD = 1 << 4
};

// MARK: - the shapes results come back in

typedef struct RlnSession RlnSession;

/// A slice of a result's `strings` blob. Not NUL-terminated: use the length.
typedef struct RlnText {
    uint32_t offset;
    uint32_t length;
} RlnText;

/// A coloured run. `start` and `length` are UTF-16 code units from the start
/// of the document; `class` is an RlnClass.
typedef struct RlnRun {
    uint32_t start;
    uint32_t length;
    uint8_t class_;
} RlnRun;

/// Free with rln_runs_free.
typedef struct RlnRuns {
    const RlnRun *items;
    size_t count;
} RlnRuns;

/// One declaration. Lists (bases, type_parameters, attributes, parameters)
/// are stretches of the blob holding their items separated by a single '\n' —
/// no C# name or type contains one, so splitting needs no escaping. Each
/// parameter reads "type name".
typedef struct RlnDeclaration {
    RlnText name;
    RlnText container;
    RlnText type_text;
    RlnText keyword;
    RlnText bases;
    RlnText type_parameters;
    RlnText attributes;
    RlnText parameters;
    /// The name's span: where a jump to this declaration lands.
    uint32_t name_start;
    uint32_t name_length;
    /// The whole declaration: what a fold collapses.
    uint32_t full_start;
    uint32_t full_length;
    uint32_t line;
    /// How deeply nested, for indenting an outline view.
    uint32_t depth;
    uint8_t kind;  // RlnDeclarationKind
    uint8_t flags; // RLN_FLAG_*
    uint16_t parameter_count;
} RlnDeclaration;

/// Free with rln_outline_free.
typedef struct RlnOutline {
    const RlnDeclaration *declarations;
    size_t count;
    const uint8_t *strings;
    size_t strings_length;
    /// Newline-separated.
    RlnText namespaces;
    /// Newline-separated; an aliased one reads "alias=name".
    RlnText usings;
    /// How many errors the parser reported. Non-zero is normal in a file
    /// being typed into; the outline is still the best available.
    uint32_t parse_errors;
} RlnOutline;

/// Somewhere to go. `path` is relative to the project root, or absolute when
/// it is outside it — an assembly the project references, most often, which
/// rln_assembly_text renders and `line` is a line of.
typedef struct RlnLocation {
    RlnText path;
    /// The fully qualified name, for showing a list of candidates.
    RlnText name;
    uint32_t line;
    /// UTF-16 code units from the start of the line.
    uint32_t character;
    uint32_t length;
    uint8_t kind; // RlnDeclarationKind
} RlnLocation;

/// Free with rln_locations_free.
typedef struct RlnLocations {
    const RlnLocation *items;
    size_t count;
    const uint8_t *strings;
    size_t strings_length;
    /// The word that was under the cursor.
    RlnText word;
    /// False when nothing in scope told the candidates apart: offer the list
    /// rather than jumping to the first of it.
    bool certain;
} RlnLocations;

/// UTF-8 text owned by the library. Free with rln_text_free.
typedef struct RlnString {
    const uint8_t *bytes;
    size_t length;
} RlnString;

/// What a reindex did. `reused` is the files that did not have to be read.
typedef struct RlnReport {
    size_t files;
    size_t reused;
    size_t parsed;
    size_t unreadable;
} RlnReport;

/// What rln_compile did.
typedef struct RlnCompiled {
    size_t files;
    size_t references;
    /// How many .csproj files described the project; zero when it was worked
    /// out without any.
    size_t projects;
    uint64_t milliseconds;
    /// 0 from project files, 1 a Unity project without them, 2 a folder of
    /// .cs files against the newest .NET installed.
    uint8_t kind;
    /// Nothing had changed since the compilation there — often one read back
    /// with rln_load_compilation — so it was kept rather than built again.
    bool unchanged;
} RlnCompiled;

/// One completion.
typedef struct RlnCompletion {
    RlnText label;
    /// The type or signature, shown beside the label.
    RlnText detail;
    uint8_t kind; // RlnCompletionKind
    /// Lower sorts first: locals, then members, then types, then keywords.
    uint8_t rank;
} RlnCompletion;

/// Free with rln_completions_free.
typedef struct RlnCompletions {
    const RlnCompletion *items;
    size_t count;
    const uint8_t *strings;
    size_t strings_length;
    /// Where the word being completed starts, in UTF-16 code units: from here
    /// to the cursor is what to filter by, and what an accepted item replaces.
    uint32_t start;
} RlnCompletions;

/// A stretch of UTF-16 code units.
typedef struct RlnRange {
    uint32_t start;
    uint32_t end;
} RlnRange;

/// Free with rln_ranges_free.
typedef struct RlnRanges {
    const RlnRange *items;
    size_t count;
} RlnRanges;

/// Something wrong in a file.
typedef struct RlnDiagnostic {
    /// UTF-16 offset and length in the text asked about.
    uint32_t start;
    uint32_t length;
    /// 1 info, 2 warning, 3 error; 0 hidden, which only comes with
    /// RLN_DIAGNOSTIC_UNNECESSARY: code to draw faded, not to list.
    uint8_t severity;
    /// RLN_DIAGNOSTIC_* bits.
    uint8_t tags;
    /// `CS0103`, or an IDE analyzer's `IDE0051`.
    RlnText code;
    RlnText message;
} RlnDiagnostic;

/// Bits in RlnDiagnostic.tags.
enum {
    /// The code can go (an unused member, a redundant cast): draw it faded.
    RLN_DIAGNOSTIC_UNNECESSARY = 1 << 0,
    /// A use of something marked [Obsolete]: strike it through.
    RLN_DIAGNOSTIC_DEPRECATED = 1 << 1,
};

/// Free with rln_diagnostics_free.
typedef struct RlnDiagnostics {
    const RlnDiagnostic *items;
    size_t count;
    const uint8_t *strings;
    size_t strings_length;
    /// The compiler looked; false means only the parser did — before the
    /// project is compiled, or for a file outside it.
    bool semantic;
} RlnDiagnostics;

/// One overload of a call.
typedef struct RlnSignature {
    /// `void Add(T item)`.
    RlnText label;
    /// Its parameters are `parameters[first_parameter ..< first_parameter +
    /// parameter_count]`, UTF-16 ranges into the label.
    uint32_t first_parameter;
    uint32_t parameter_count;
} RlnSignature;

/// Free with rln_signatures_free.
typedef struct RlnSignatures {
    const RlnSignature *items;
    size_t count;
    const RlnRange *parameters;
    size_t parameter_count;
    const uint8_t *strings;
    size_t strings_length;
    /// The overload the arguments so far fit best, and the parameter the
    /// cursor is at.
    uint32_t active;
    uint32_t parameter;
} RlnSignatures;

/// A documented parameter.
typedef struct RlnDocParameter {
    RlnText name;
    RlnText text;
} RlnDocParameter;

/// Free with rln_documentation_free. Plain text: tags gone, references
/// shown as the names they point to, paragraphs split by a blank line.
typedef struct RlnDocumentation {
    RlnText signature;
    /// Where it is declared: the qualified name of its type or namespace.
    RlnText container;
    RlnText summary;
    RlnText returns;
    const RlnDocParameter *parameters;
    size_t parameter_count;
    const uint8_t *strings;
    size_t strings_length;
} RlnDocumentation;

/// One replacement: `length` UTF-16 code units at `start` of `path` become
/// `text`.
typedef struct RlnEdit {
    /// Absolute.
    RlnText path;
    RlnText text;
    uint32_t start;
    uint32_t length;
} RlnEdit;

/// A file to rename, for a type whose file follows its name.
typedef struct RlnRename {
    RlnText from;
    RlnText to;
} RlnRename;

/// Edits across the project. Within a file they are in order and never
/// overlap: apply them from the last to the first. Offsets count in the text
/// the question was asked with for that file, and in its saved text for any
/// other. Free with rln_edits_free.
typedef struct RlnEdits {
    const RlnEdit *items;
    size_t count;
    const RlnRename *renames;
    size_t rename_count;
    const uint8_t *strings;
    size_t strings_length;
} RlnEdits;

typedef enum RlnActionKind {
    RLN_ACTION_QUICK_FIX = 0,
    RLN_ACTION_REFACTOR,
    RLN_ACTION_EXTRACT,
    RLN_ACTION_INLINE,
    RLN_ACTION_REWRITE,
    RLN_ACTION_ORGANIZE,
    RLN_ACTION_GENERATE,
} RlnActionKind;

/// One entry of the light bulb: its edits are `edit_count` items of the
/// shared `edits` array from `first_edit`, and likewise its renames.
typedef struct RlnCodeAction {
    RlnText title;
    /// The diagnostic code it fixes; empty for a refactoring.
    RlnText fixes;
    uint32_t first_edit;
    uint32_t edit_count;
    uint32_t first_rename;
    uint32_t rename_count;
    /// An RlnActionKind.
    uint8_t kind;
} RlnCodeAction;

/// Free with rln_code_actions_free.
typedef struct RlnCodeActions {
    const RlnCodeAction *items;
    size_t count;
    const RlnEdit *edits;
    size_t edit_count;
    const RlnRename *renames;
    size_t rename_count;
    const uint8_t *strings;
    size_t strings_length;
} RlnCodeActions;

/// What the cache has been doing, for a status line.
typedef struct RlnStatistics {
    /// Answers kept on the strength of the file's stamp alone.
    uint64_t stamped;
    /// Answers kept because the bytes hashed the same although the stamp moved.
    uint64_t rehashed;
    /// Answers read back from the cache directory.
    uint64_t from_disk;
    /// Answers that had to be computed.
    uint64_t computed;
    size_t entries;
    size_t bytes;
} RlnStatistics;

// MARK: - a session

/// Opens a session over a project.
///
/// `cache_directory` may be null, in which case nothing survives the process.
/// `symbols` may be null when `symbol_count` is zero. The symbols decide
/// which branch of an #if is live, and so what is coloured, outlined and
/// indexed at all — two sessions with different ones share no cached answers.
///
/// Returns null when an argument is null or not UTF-8.
RlnSession *rln_session_new(const char *root,
                            const char *cache_directory,
                            const char *const *symbols,
                            size_t symbol_count);

/// Keeps decompiled assemblies in `directory`, shared by every session given
/// the same one, rather than in the project's cache: an engine's assembly is
/// the same file in every project. Call once, before the first assembly is
/// asked for. RLN_BAD_ARGUMENT for a null argument or when it was set already.
RlnStatus rln_session_share_assembly_cache(RlnSession *session, const char *directory);

/// Closes a session. Null is allowed and does nothing.
void rln_session_free(RlnSession *session);

/// Copies the message from the last failure in this session. Free with
/// rln_text_free. Empty when nothing has failed.
RlnString rln_last_error(RlnSession *session);

void rln_text_free(RlnString text);

RlnStatistics rln_statistics(RlnSession *session);

// MARK: - layer 1: open the file

/// Reads and decodes a file. Does not parse, lex or index it.
RlnStatus rln_open(RlnSession *session, const char *path);

/// Opens a buffer whose text you already hold — one being typed into, or one
/// that was never on disk.
RlnStatus rln_open_text(RlnSession *session, const char *path, const char *text);

/// Replaces an open file's text. Everything worked out about the old text is
/// dropped, the colouring checkpoints included, so this is for a settled
/// edit rather than for every keystroke.
RlnStatus rln_set_text(RlnSession *session, const char *path, const char *text);

void rln_close(RlnSession *session, const char *path);

// MARK: - layer 2: colour the screen

/// Colours lines `first` through `last`, both inclusive and zero-based.
///
/// Costs what the window costs, not what the file costs: the lexer resumes
/// from a checkpoint above the window rather than starting at the top. Runs
/// with no colour of their own are left out — the editor's default covers
/// them, and they are most of the file.
RlnStatus rln_classify(RlnSession *session,
                       const char *path,
                       uint32_t first,
                       uint32_t last,
                       RlnRuns *out);

void rln_runs_free(RlnRuns runs);

/// Walks the whole file, laying down every checkpoint, so that a jump to any
/// line becomes as cheap as a scroll. For a background thread.
RlnStatus rln_warm(RlnSession *session, const char *path);

// MARK: - layer 3: what the file declares

/// The outline of an open file, from the parser rather than from the shape of
/// its lines. Free with rln_outline_free.
RlnStatus rln_outline(RlnSession *session, const char *path, RlnOutline *out);

void rln_outline_free(RlnOutline outline);

// MARK: - layer 4: the project

/// Builds the project index. Files unchanged since the last build come back
/// from the cache rather than being parsed, so this is cheap after a save and
/// expensive only the first time. `out` may be null.
RlnStatus rln_reindex(RlnSession *session,
                      const char *const *paths,
                      size_t count,
                      RlnReport *out);

/// Where the name at `offset` was declared. `offset` is in UTF-16 code units.
///
/// Free with rln_locations_free. A refusal is worth telling apart: RLN_NOT_A_NAME
/// means the cursor is on punctuation or inside a string, RLN_RECEIVER_UNKNOWN
/// means the left of a `.` could not be typed, and RLN_NOT_IN_PROJECT usually
/// means an assembly, which the layer 5 calls can open.
RlnStatus rln_definition(RlnSession *session,
                         const char *path,
                         uint32_t offset,
                         RlnLocations *out);

/// What derives from, or overrides, whatever is at `offset`.
RlnStatus rln_implementations(RlnSession *session,
                              const char *path,
                              uint32_t offset,
                              RlnLocations *out);

void rln_locations_free(RlnLocations locations);

// MARK: - layer 6: what the code means

/// Compiles the project: reads what its .sln/.csproj (or Unity editor, or
/// nothing) says about references and symbols, and declares every file it
/// compiles against them. `paths` are the files the editor knows of; zero of
/// them means the index's. Blocks for as long as that takes — seconds on a
/// large project — so call it from a background thread, after rln_reindex
/// and again after a save: the compilation it replaces keeps answering until
/// it is done, and unchanged files are not parsed again. `out` may be null.
RlnStatus rln_compile(RlnSession *session,
                      const char *const *paths,
                      size_t count,
                      RlnCompiled *out);

/// Writes the compilation to the session's cache directory, if it changed
/// since it was last written or read — for when the project closes. The file
/// is written aside and renamed into place, so an interrupted write leaves
/// the old one.
RlnStatus rln_save_compilation(RlnSession *session);

/// Reads back the compilation the last run wrote and installs it, so the
/// compiler answers straight away: reading it is a fraction of compiling.
/// It may be out of date; the next rln_compile finds out, keeping it when
/// nothing changed (`unchanged`) and replacing it otherwise. RLN_NOT_COMPILED
/// when there is none, it is damaged, or another build of the library wrote
/// it. `out` may be null.
RlnStatus rln_load_compilation(RlnSession *session, RlnCompiled *out);

/// Where the name at `offset` was declared: the overload a call chose, the
/// member a `var` turned out to have — or its line in an assembly, for a name
/// from one. `text` is the editor's unsaved copy of the file, or null for the
/// file as compiled; `offset` is into whichever that is, and so are the
/// places in this file that come back.
///
/// Answers from the index when the project is not compiled yet or the
/// compiler does not know. Free with rln_locations_free.
RlnStatus rln_definition_in(RlnSession *session,
                            const char *path,
                            const char *text,
                            uint32_t offset,
                            RlnLocations *out);

/// Every use of the name at `offset` across the project, its declarations
/// among them. `text` as for rln_definition_in. RLN_NOT_COMPILED before
/// rln_compile has finished once. Free with rln_locations_free.
RlnStatus rln_references(RlnSession *session,
                         const char *path,
                         const char *text,
                         uint32_t offset,
                         RlnLocations *out);

/// What can be written at `offset`: the members of the type left of a `.`,
/// or what is in scope. `text` as for rln_definition_in — and it is almost
/// always the unsaved copy, since completion is asked while typing. Free
/// with rln_completions_free.
RlnStatus rln_completions(RlnSession *session,
                          const char *path,
                          const char *text,
                          uint32_t offset,
                          RlnCompletions *out);

void rln_completions_free(RlnCompletions completions);

/// The name at `offset` as one line, `int Count` or `void Add(T item)`. Free
/// with rln_text_free.
RlnStatus rln_describe(RlnSession *session,
                       const char *path,
                       const char *text,
                       uint32_t offset,
                       RlnString *out);

/// What is wrong with the file as the editor has it — `text` as for
/// rln_definition_in: its syntax errors and, once the project is compiled,
/// what declaring and binding it finds. Parses and binds the whole file, so
/// ask from a background thread after typing pauses. Free with
/// rln_diagnostics_free.
RlnStatus rln_diagnostics(RlnSession *session,
                          const char *path,
                          const char *text,
                          RlnDiagnostics *out);

void rln_diagnostics_free(RlnDiagnostics diagnostics);

/// The overloads of the call whose argument list holds `offset`, for showing
/// while the arguments are typed. RLN_NOT_A_NAME outside an argument list.
/// Free with rln_signatures_free.
RlnStatus rln_signatures(RlnSession *session,
                         const char *path,
                         const char *text,
                         uint32_t offset,
                         RlnSignatures *out);

void rln_signatures_free(RlnSignatures signatures);

/// The documentation of the name at `offset`: its `///` comment, or the XML
/// file beside the assembly it comes from. Free with rln_documentation_free.
RlnStatus rln_documentation(RlnSession *session,
                            const char *path,
                            const char *text,
                            uint32_t offset,
                            RlnDocumentation *out);

void rln_documentation_free(RlnDocumentation documentation);

/// Ever larger pieces of code around `start..end` (UTF-16), smallest first —
/// what extend selection steps through. Syntax only: works before the
/// project is compiled. Free with rln_ranges_free.
RlnStatus rln_selection_ranges(RlnSession *session,
                               const char *path,
                               const char *text,
                               uint32_t start,
                               uint32_t end,
                               RlnRanges *out);

void rln_ranges_free(RlnRanges ranges);

// MARK: - edits: what the editor is asked to do

void rln_edits_free(RlnEdits edits);

/// Whether `path` is source a generator wrote — in a Unity project, what its
/// source generators left in Temp/GeneratedCode or the folder Unity's build
/// names. Such files are compiled, so go-to-definition and references reach
/// them, but no call ever edits them: open them read-only.
bool rln_is_generated(RlnSession *session, const char *path);

/// What the light bulb offers for `start..end` (UTF-16; equal for a cursor):
/// fixes for the diagnostics there and refactorings of the selection, each
/// with its edits. Needs a compilation. Free with rln_code_actions_free.
RlnStatus rln_code_actions(RlnSession *session,
                           const char *path,
                           const char *text,
                           uint32_t start,
                           uint32_t end,
                           RlnCodeActions *out);

void rln_code_actions_free(RlnCodeActions actions);

// MARK: - semantic colouring, highlights, detailed references, code lens

/// What a name is, as Roslyn's ClassificationTypeNames has it. Mirrors
/// `SemanticClass`; check the count with rln_semantic_class_count().
typedef enum RlnSemanticClass {
    RLN_SEMANTIC_CLASS_NAME = 0,
    RLN_SEMANTIC_RECORD_CLASS_NAME = 1,
    RLN_SEMANTIC_STRUCT_NAME = 2,
    RLN_SEMANTIC_RECORD_STRUCT_NAME = 3,
    RLN_SEMANTIC_INTERFACE_NAME = 4,
    RLN_SEMANTIC_ENUM_NAME = 5,
    RLN_SEMANTIC_DELEGATE_NAME = 6,
    RLN_SEMANTIC_TYPE_PARAMETER_NAME = 7,
    RLN_SEMANTIC_NAMESPACE_NAME = 8,
    RLN_SEMANTIC_METHOD_NAME = 9,
    RLN_SEMANTIC_EXTENSION_METHOD_NAME = 10,
    RLN_SEMANTIC_PROPERTY_NAME = 11,
    RLN_SEMANTIC_EVENT_NAME = 12,
    RLN_SEMANTIC_FIELD_NAME = 13,
    RLN_SEMANTIC_CONSTANT_NAME = 14,
    RLN_SEMANTIC_ENUM_MEMBER_NAME = 15,
    RLN_SEMANTIC_LOCAL_NAME = 16,
    RLN_SEMANTIC_PARAMETER_NAME = 17,
    RLN_SEMANTIC_LABEL_NAME = 18,
    /// A contextual keyword acting as one: `var`, `nameof`, `dynamic`,
    /// `global::`, `async`, `await`, `yield`, `record`.
    RLN_SEMANTIC_KEYWORD = 19
} RlnSemanticClass;

/// Bits in RlnSemanticRun.modifiers.
enum {
    /// Roslyn's "static symbol": a static member or type, or a constant.
    RLN_MODIFIER_STATIC = 1 << 0,
    /// Roslyn's "reassigned variable": a local or parameter written after
    /// its declaration.
    RLN_MODIFIER_REASSIGNED = 1 << 1,
    /// Declared with [Obsolete].
    RLN_MODIFIER_DEPRECATED = 1 << 2,
    RLN_MODIFIER_ABSTRACT = 1 << 3,
    /// readonly or const.
    RLN_MODIFIER_READONLY = 1 << 4,
    RLN_MODIFIER_ASYNC = 1 << 5,
    /// The name its declaration gives, not a use of it.
    RLN_MODIFIER_DECLARATION = 1 << 6,
    /// From a referenced assembly rather than the project.
    RLN_MODIFIER_DEFAULT_LIBRARY = 1 << 7
};

/// What a highlighted span is, as Roslyn's HighlightSpanKind has it.
typedef enum RlnHighlightKind {
    /// A keyword of the construct under the cursor.
    RLN_HIGHLIGHT_TEXT = 0,
    RLN_HIGHLIGHT_DEFINITION = 1,
    RLN_HIGHLIGHT_REFERENCE = 2,
    RLN_HIGHLIGHT_WRITTEN_REFERENCE = 3
} RlnHighlightKind;

/// How a reference touches what it names.
typedef enum RlnReferenceKind {
    RLN_REFERENCE_DEFINITION = 0,
    /// Assigned, incremented, passed by ref or out, deconstructed into.
    RLN_REFERENCE_WRITE = 1,
    RLN_REFERENCE_READ = 2
} RlnReferenceKind;

/// A name coloured by what it refers to, in UTF-16 code units.
typedef struct RlnSemanticRun {
    uint32_t start;
    uint32_t length;
    /// RLN_MODIFIER_* bits.
    uint32_t modifiers;
    /// An RlnSemanticClass.
    uint8_t class_;
} RlnSemanticRun;

/// Free with rln_semantic_runs_free.
typedef struct RlnSemanticRuns {
    const RlnSemanticRun *items;
    size_t count;
} RlnSemanticRuns;

/// A span to highlight, in UTF-16 code units.
typedef struct RlnHighlight {
    uint32_t start;
    uint32_t length;
    /// An RlnHighlightKind.
    uint8_t kind;
} RlnHighlight;

/// Free with rln_highlights_free.
typedef struct RlnHighlights {
    const RlnHighlight *items;
    size_t count;
} RlnHighlights;

/// One entry of a references list.
typedef struct RlnReference {
    /// Relative to the project root.
    RlnText path;
    /// The member or type the reference is in: `Arena.Fight`.
    RlnText container;
    /// Its line, trimmed.
    RlnText preview;
    uint32_t line;
    /// UTF-16 code units from the start of the line.
    uint32_t character;
    uint32_t length;
    /// An RlnReferenceKind.
    uint8_t kind;
} RlnReference;

/// Free with rln_references_free.
typedef struct RlnReferences {
    const RlnReference *items;
    size_t count;
    const uint8_t *strings;
    size_t strings_length;
    /// The word that was under the cursor.
    RlnText word;
} RlnReferences;

/// A reference count over a declaration's name, in UTF-16 code units.
typedef struct RlnLens {
    uint32_t start;
    uint32_t length;
    uint32_t count;
} RlnLens;

/// Free with rln_lenses_free.
typedef struct RlnLenses {
    const RlnLens *items;
    size_t count;
} RlnLenses;

/// The names in `start..end` (UTF-16) of the file as the editor has it —
/// `text` as for rln_definition_in — coloured by what they refer to: the
/// layer above rln_classify, for the same window. Only the bodies in the
/// range are bound. Names nothing binds are left out, for the syntactic
/// colour to stand. Free with rln_semantic_runs_free.
RlnStatus rln_semantic_tokens(RlnSession *session,
                              const char *path,
                              const char *text,
                              uint32_t start,
                              uint32_t end,
                              RlnSemanticRuns *out);

void rln_semantic_runs_free(RlnSemanticRuns runs);

/// What to highlight for the cursor at `offset`: every occurrence in the
/// file of the symbol under it, as definition, read or write; or, on a
/// keyword (if/else, loops with their break/continue, return/yield, switch,
/// try/catch/finally, async/await, #if/#endif, #region), the keywords of its
/// construct. Keywords need no compilation. Free with rln_highlights_free.
RlnStatus rln_highlights(RlnSession *session,
                         const char *path,
                         const char *text,
                         uint32_t offset,
                         RlnHighlights *out);

void rln_highlights_free(RlnHighlights highlights);

/// Every reference to the name at `offset` across the project, each with
/// whether it declares, writes or reads, the member it is in and its line.
/// Overrides and implementations of a member are included, their
/// declarations as definitions; so are `new()` calls, `nameof`, crefs and
/// attributes. Free with rln_references_free.
RlnStatus rln_references_detailed(RlnSession *session,
                                  const char *path,
                                  const char *text,
                                  uint32_t offset,
                                  RlnReferences *out);

void rln_references_free(RlnReferences references);

/// How many references each type, method, constructor, property and event
/// declared in the file has across the project: a code lens. Searches the
/// project once for all of them; still, ask from a background thread. Free
/// with rln_lenses_free.
RlnStatus rln_code_lens(RlnSession *session,
                        const char *path,
                        const char *text,
                        RlnLenses *out);

/// Calls off every rln_code_lens running on the session: each stops at the
/// next file it would search and returns RLN_CANCELLED. One begun after this
/// call is not affected. Any thread — it is meant for the one that is not
/// waiting for the count.
void rln_cancel_code_lens(RlnSession *session);

/// Where rln_code_lens puts its counts, in the same order, without counting:
/// every count is UINT32_MAX. Only this file is looked at, so it is cheap
/// enough to ask while the file opens, to make room for the lenses before
/// the counts come. Free with rln_lenses_free.
RlnStatus rln_code_lens_places(RlnSession *session,
                               const char *path,
                               const char *text,
                               RlnLenses *out);

void rln_lenses_free(RlnLenses lenses);

/// The number of RlnSemanticClass values this library knows.
uint32_t rln_semantic_class_count(void);

// MARK: - rename

/// Whether the name at the cursor can be renamed, and where it is. Free
/// with rln_rename_info_free.
typedef struct RlnRenameInfo {
    /// UTF-16 offset and length of the name: where the rename box goes.
    uint32_t start;
    uint32_t length;
    /// The name as written (`@class` for an escaped keyword).
    RlnText text;
    /// What is being renamed, as one line: `class Game.Pawn`.
    RlnText description;
    /// Why it cannot be renamed; empty when it can.
    RlnText refused;
    uint8_t can_rename;
    const uint8_t *strings;
    size_t strings_length;
} RlnRenameInfo;

/// A place the rename would break, or — `resolved` set — one it already
/// put right by qualifying the name (`this.name`).
typedef struct RlnConflict {
    RlnText path;
    RlnText message;
    /// UTF-16, in the text the edits to that file count in.
    uint32_t start;
    uint32_t length;
    uint8_t resolved;
} RlnConflict;

/// A rename: the edits and files to rename, as any RlnEdits, and its
/// conflicts. The conflicts' texts and `refused` are in `edits.strings`.
/// Free with rln_rename_result_free, not rln_edits_free.
typedef struct RlnRenameResult {
    RlnEdits edits;
    const RlnConflict *conflicts;
    size_t conflict_count;
    /// Why nothing was renamed; empty when it was.
    RlnText refused;
} RlnRenameResult;

/// What a rename does besides renaming code: Roslyn's check boxes.
enum {
    /// The name as a whole word in comments.
    RLN_RENAME_IN_COMMENTS = 1,
    /// The name as a whole word in strings.
    RLN_RENAME_IN_STRINGS = 2,
    /// Every overload of a method.
    RLN_RENAME_OVERLOADS = 4,
    /// The file of a type, when it is named after the type.
    RLN_RENAME_FILE = 8,
};

/// Whether what is at `offset` (UTF-16) can be renamed. A name that cannot
/// be is RLN_OK with `can_rename` clear and the reason in `refused`. Needs a
/// compilation.
RlnStatus rln_prepare_rename(RlnSession *session,
                             const char *path,
                             const char *text,
                             uint32_t offset,
                             RlnRenameInfo *out);

void rln_rename_info_free(RlnRenameInfo info);

/// Renames what is at `offset` (UTF-16) of `path` — whose text is `text`,
/// or NULL for the saved one — to `new_name`, across the project. `flags`
/// are RLN_RENAME_*. A rename that cannot be done (not a name, not a valid
/// identifier) is RLN_OK with the reason in `refused` and no edits. Free with
/// rln_rename_result_free.
RlnStatus rln_rename(RlnSession *session,
                     const char *path,
                     const char *text,
                     uint32_t offset,
                     const char *new_name,
                     uint32_t flags,
                     RlnRenameResult *out);

void rln_rename_result_free(RlnRenameResult result);

// MARK: - navigation: type definition, bases, implementations, hierarchies, search

/// What rln_search looks among.
typedef enum RlnSearchKind {
    RLN_SEARCH_ALL = 0,
    RLN_SEARCH_TYPES = 1,
    RLN_SEARCH_MEMBERS = 2,
    RLN_SEARCH_FILES = 3
} RlnSearchKind;

/// How well a pattern matched, best first, as Roslyn ranks them.
typedef enum RlnMatchKind {
    RLN_MATCH_EXACT = 0,
    RLN_MATCH_PREFIX = 1,
    /// The start of a word inside the name: `Def` in `GoToDefinition`.
    RLN_MATCH_START_OF_WORD = 2,
    /// The start of every word: `GTD`, `gtDef`.
    RLN_MATCH_CAMEL_CASE_EXACT = 3,
    RLN_MATCH_CAMEL_CASE_PREFIX = 4,
    RLN_MATCH_CAMEL_CASE_NON_CONTIGUOUS_PREFIX = 5,
    RLN_MATCH_CAMEL_CASE_SUBSTRING = 6,
    RLN_MATCH_CAMEL_CASE_NON_CONTIGUOUS_SUBSTRING = 7,
    RLN_MATCH_SUBSTRING = 8,
    /// One letter wrong, missing, extra or swapped.
    RLN_MATCH_FUZZY = 9
} RlnMatchKind;

/// A node of a call or type hierarchy.
typedef struct RlnHierarchyItem {
    RlnText name;
    /// The signature: `double Area()`, `class Circle`.
    RlnText detail;
    /// The qualified name of the type or namespace it is in.
    RlnText container;
    /// Pass it to rln_incoming_calls, rln_outgoing_calls, rln_supertypes or
    /// rln_subtypes to expand the item. It names the symbol, not a place, so
    /// it still works after the project has been compiled again.
    RlnText key;
    /// Relative to the project root, or an assembly's path. Empty when
    /// `has_location` is false.
    RlnText path;
    /// The name, which a jump selects: line, UTF-16 column and length.
    uint32_t line;
    uint32_t character;
    uint32_t length;
    /// The whole declaration.
    uint32_t start_line;
    uint32_t start_character;
    uint32_t end_line;
    uint32_t end_character;
    uint8_t kind; // RlnDeclarationKind
    bool has_location;
} RlnHierarchyItem;

/// Free with rln_hierarchy_items_free.
typedef struct RlnHierarchyItems {
    const RlnHierarchyItem *items;
    size_t count;
    const uint8_t *strings;
    size_t strings_length;
} RlnHierarchyItems;

/// From one line and column to another; columns in UTF-16 code units.
typedef struct RlnLineRange {
    uint32_t start_line;
    uint32_t start_character;
    uint32_t end_line;
    uint32_t end_character;
} RlnLineRange;

/// A caller (incoming) or a callee (outgoing), with the calls: `range_count`
/// of RlnCalls.ranges from `first_range`, in the file `path`.
typedef struct RlnCall {
    RlnHierarchyItem item;
    RlnText path;
    uint32_t first_range;
    uint32_t range_count;
    /// The calls name a member the one asked about overrides or implements —
    /// `shape.Area()` for `Circle.Area` — so they may reach it and may not.
    bool through_base;
} RlnCall;

/// Free with rln_calls_free.
typedef struct RlnCalls {
    const RlnCall *items;
    size_t count;
    const RlnLineRange *ranges;
    size_t range_count;
    const uint8_t *strings;
    size_t strings_length;
} RlnCalls;

/// One Navigate To result: `range_count` of RlnSearchResults.ranges from
/// `first_range` are the UTF-16 ranges of `name` that matched.
typedef struct RlnSearchResult {
    /// Where to go; line 0 for a file. `location.name` is the qualified name.
    RlnLocation location;
    RlnText name;
    RlnText container;
    uint32_t first_range;
    uint32_t range_count;
    uint8_t match_kind; // RlnMatchKind
    bool case_sensitive;
    bool is_file;
} RlnSearchResult;

/// Free with rln_search_results_free.
typedef struct RlnSearchResults {
    const RlnSearchResult *items;
    size_t count;
    const RlnRange *ranges;
    size_t range_count;
    const uint8_t *strings;
    size_t strings_length;
} RlnSearchResults;

/// Where the type of the name at `offset` is declared: a variable's type, a
/// member's, a call's result; an array's element type and a generic type's
/// arguments too. `text` as for rln_definition_in. Free with
/// rln_locations_free.
RlnStatus rln_type_definition(RlnSession *session,
                              const char *path,
                              const char *text,
                              uint32_t offset,
                              RlnLocations *out);

/// What the type or member at `offset` derives from: base classes and
/// interfaces, or the members it overrides and implements. Nearest first.
/// Free with rln_locations_free.
RlnStatus rln_bases(RlnSession *session,
                    const char *path,
                    const char *text,
                    uint32_t offset,
                    RlnLocations *out);

/// What implements the type or member at `offset` across the project: the
/// compiler's answer once compiled, the index's (rln_implementations) before.
/// Free with rln_locations_free.
RlnStatus rln_implementations_in(RlnSession *session,
                                 const char *path,
                                 const char *text,
                                 uint32_t offset,
                                 RlnLocations *out);

/// The project's types derived from the type at `offset`, however
/// indirectly: classes and structs, or the interfaces extending it when
/// `interfaces` is true. Free with rln_locations_free.
RlnStatus rln_derived_types(RlnSession *session,
                            const char *path,
                            const char *text,
                            uint32_t offset,
                            bool interfaces,
                            RlnLocations *out);

/// The method, constructor, property, event or field at `offset` as the root
/// of a call hierarchy: one item. Free with rln_hierarchy_items_free.
RlnStatus rln_call_hierarchy(RlnSession *session,
                             const char *path,
                             const char *text,
                             uint32_t offset,
                             RlnHierarchyItems *out);

/// Every member of the project that calls the one `key` names, with where;
/// then those calling what it overrides or implements, marked through_base.
/// RLN_NOT_IN_PROJECT when the key names nothing any more. Free with
/// rln_calls_free.
RlnStatus rln_incoming_calls(RlnSession *session, const char *key, RlnCalls *out);

/// What the member `key` names calls, with where, in order. Free with
/// rln_calls_free.
RlnStatus rln_outgoing_calls(RlnSession *session, const char *key, RlnCalls *out);

void rln_calls_free(RlnCalls calls);

/// The type at `offset`, or the type of what is there, as the root of a
/// type hierarchy: one item. Free with rln_hierarchy_items_free.
RlnStatus rln_type_hierarchy(RlnSession *session,
                             const char *path,
                             const char *text,
                             uint32_t offset,
                             RlnHierarchyItems *out);

/// The base class and interfaces of the type `key` names, those in assemblies
/// among them. Free with rln_hierarchy_items_free.
RlnStatus rln_supertypes(RlnSession *session, const char *key, RlnHierarchyItems *out);

/// The project's types naming the type `key` names as a base. Free with
/// rln_hierarchy_items_free.
RlnStatus rln_subtypes(RlnSession *session, const char *key, RlnHierarchyItems *out);

void rln_hierarchy_items_free(RlnHierarchyItems items);

/// Navigate To: declarations and files whose names `pattern` matches — a
/// prefix, the capitals (`GTD`), the starts of words (`gtDef`), letters from
/// the middle, one typo — best first, at most `limit`. `Type.Member` matches
/// the container too. `kind` is an RlnSearchKind. Answers from the index, so
/// it works before rln_compile. Free with rln_search_results_free.
RlnStatus rln_search(RlnSession *session,
                     const char *pattern,
                     uint8_t kind,
                     uint32_t limit,
                     RlnSearchResults *out);

void rln_search_results_free(RlnSearchResults results);

// MARK: - syntax-level editing: formatting, structure, braces, comments
//
// None of these needs a compilation: each parses the one file asked about
// (`text` when given, the open or saved file when null) and answers from the
// tree. Offsets are UTF-16.

/// The edits that format the whole file, with Roslyn's default rules and the
/// file's own indentation and line breaks. Free with rln_edits_free.
RlnStatus rln_format_document(RlnSession *session,
                              const char *path,
                              const char *text,
                              RlnEdits *out);

/// The edits that format the lines `start..end` touches, and nothing else.
/// Free with rln_edits_free.
RlnStatus rln_format_range(RlnSession *session,
                           const char *path,
                           const char *text,
                           uint32_t start,
                           uint32_t end,
                           RlnEdits *out);

/// What typing `typed` (a Unicode scalar) reformats, with `position` the
/// caret just after it and `text` already holding it: `;` the statement it
/// ends, `}` the construct it closes, '\n' the new line and the one before,
/// '#' the directive. Anything else: no edits. Free with rln_edits_free.
RlnStatus rln_format_on_type(RlnSession *session,
                             const char *path,
                             const char *text,
                             uint32_t position,
                             uint32_t typed,
                             RlnEdits *out);

/// The indentation for the new line when Enter is pressed at `position`
/// (in the text before the line break goes in). `bytes` is NULL when there
/// is no opinion, as inside a string over several lines; an empty non-NULL
/// text is the first column. Free with rln_text_free.
RlnStatus rln_indentation_for_new_line(RlnSession *session,
                                       const char *path,
                                       const char *text,
                                       uint32_t position,
                                       RlnString *out);

typedef enum RlnFoldKind {
    RLN_FOLD_IMPORTS = 0,
    RLN_FOLD_NAMESPACE,
    RLN_FOLD_TYPE,
    RLN_FOLD_MEMBER,
    RLN_FOLD_STATEMENT,
    RLN_FOLD_CONDITIONAL,
    RLN_FOLD_LOOP,
    RLN_FOLD_EXPRESSION,
    RLN_FOLD_COMMENT,
    RLN_FOLD_REGION,
    RLN_FOLD_NONSTRUCTURAL,
} RlnFoldKind;

/// One foldable block: `start..end` folds away (from the end of the header
/// line to the closing brace), `hint_start..hint_end` is the whole construct
/// for a tooltip, and `banner` stands in for the folded text.
typedef struct RlnFoldingRange {
    uint32_t start;
    uint32_t end;
    uint32_t hint_start;
    uint32_t hint_end;
    RlnText banner;
    /// An RlnFoldKind.
    uint8_t kind;
    bool collapsible;
    bool collapsed_by_default;
} RlnFoldingRange;

/// Free with rln_folding_ranges_free.
typedef struct RlnFoldingRanges {
    const RlnFoldingRange *items;
    size_t count;
    const uint8_t *strings;
    size_t strings_length;
} RlnFoldingRanges;

/// Every foldable block of the file, in order: declarations, statements,
/// lambdas, initializers, `using` groups, comments, regions, disabled text,
/// strings over several lines. `collapse_usings` makes the `using`
/// directives start folded; regions always do.
RlnStatus rln_block_structure(RlnSession *session,
                              const char *path,
                              const char *text,
                              bool collapse_usings,
                              RlnFoldingRanges *out);

void rln_folding_ranges_free(RlnFoldingRanges ranges);

/// The number of RlnFoldKind values this library knows.
uint32_t rln_fold_kind_count(void);

/// Two delimiters that belong together. All zero, and `found` false, when
/// the caret is beside none.
typedef struct RlnBracePair {
    uint32_t open_start;
    uint32_t open_end;
    uint32_t close_start;
    uint32_t close_end;
    bool found;
} RlnBracePair;

/// The pair the delimiter beside `position` belongs to — braces,
/// parentheses, brackets, the angle brackets of generics, quotes, and
/// #if/#elif/#else/#endif and #region/#endregion. The token on the caret's
/// right is tried first, then the one on its left.
RlnStatus rln_brace_match(RlnSession *session,
                          const char *path,
                          const char *text,
                          uint32_t position,
                          RlnBracePair *out);

/// Documentation to write, and the caret once it is written (in the text
/// after the edits). Empty, and `found` false, when there is nothing to
/// write. Free with rln_snippet_free.
typedef struct RlnSnippet {
    RlnEdits edits;
    uint32_t caret;
    bool found;
} RlnSnippet;

/// What typing the third `/` of `///` expands into: the summary, params,
/// type params and returns of the declaration below. `position` is the
/// caret after the slash.
RlnStatus rln_doc_comment_on_typed(RlnSession *session,
                                   const char *path,
                                   const char *text,
                                   uint32_t position,
                                   RlnSnippet *out);

/// What Enter adds inside documentation: `/// ` on the new line, or the
/// whole skeleton after a lone `///`. `position` is the start of the new
/// line, and the line break is already in `text`.
RlnStatus rln_doc_comment_on_enter(RlnSession *session,
                                   const char *path,
                                   const char *text,
                                   uint32_t position,
                                   RlnSnippet *out);

/// The "insert comment" command: documentation above the declaration around
/// `position`.
RlnStatus rln_insert_doc_comment(RlnSession *session,
                                 const char *path,
                                 const char *text,
                                 uint32_t position,
                                 RlnSnippet *out);

void rln_snippet_free(RlnSnippet snippet);

/// Comments the lines of `start..end` with `//`, or uncomments them when
/// every one is. Free with rln_edits_free.
RlnStatus rln_toggle_line_comment(RlnSession *session,
                                  const char *path,
                                  const char *text,
                                  uint32_t start,
                                  uint32_t end,
                                  RlnEdits *out);

/// Wraps `start..end` in `/* */`, or unwraps the block comments it is. With
/// no selection: the line's code, or the comment the caret is in. Free with
/// rln_edits_free.
RlnStatus rln_toggle_block_comment(RlnSession *session,
                                   const char *path,
                                   const char *text,
                                   uint32_t start,
                                   uint32_t end,
                                   RlnEdits *out);

// MARK: - completion parity

/// One completion with everything needed to commit it. An empty insert_text
/// or filter_text means the label; an empty commit_characters means the
/// editor's usual ones.
typedef struct RlnCompletionItem {
    RlnText label;
    /// The type or signature, shown beside the label.
    RlnText detail;
    /// What to write in place of the word: `List<int>`, `@class`, a whole
    /// override.
    RlnText insert_text;
    /// What the typed word is matched against.
    RlnText filter_text;
    /// Characters that also commit this item, each one a character.
    RlnText commit_characters;
    /// This item's other edits — the `using` an unimported type needs, the
    /// modifiers an override rewrites — as edits[edits_start ..
    /// edits_start + edits_count] of the list.
    uint32_t edits_start;
    uint32_t edits_count;
    /// Where the cursor goes, in UTF-16 code units into the inserted text;
    /// UINT32_MAX for its end.
    uint32_t caret;
    uint8_t kind; // RlnCompletionKind
    /// Lower sorts first.
    uint8_t rank;
    /// The item to select when the list opens.
    uint8_t preselect;
    /// insert_text is a template with the caret inside it.
    uint8_t is_snippet;
} RlnCompletionItem;

/// One replacement in the file asked about: `length` UTF-16 code units at
/// `start` become `text`. Never overlapping the word being completed.
typedef struct RlnTextEdit {
    uint32_t start;
    uint32_t length;
    RlnText text;
} RlnTextEdit;

/// Free with rln_completion_items_free.
typedef struct RlnCompletionItems {
    const RlnCompletionItem *items;
    size_t count;
    const RlnTextEdit *edits;
    size_t edit_count;
    const uint8_t *strings;
    size_t strings_length;
    /// Where the word being completed starts, in UTF-16 code units.
    uint32_t start;
    /// A new name is being written: the items are suggestions, and a space
    /// or punctuation must not commit one.
    uint8_t suggestion_mode;
} RlnCompletionItems;

/// What can be written at `offset` (UTF-16), the way Roslyn's completion
/// service answers: keywords only where the grammar allows them, types only
/// where only a type goes, the expected type or enum members preselected,
/// overrides and partial methods written out, named arguments, object
/// initializer members, types from namespaces not imported (with the
/// `using` to add), tags in `///` comments, `#` directives, snippets, and
/// names for a new variable. `text` is the editor's text, or NULL for the
/// saved one. Free with rln_completion_items_free.
RlnStatus rln_completions_ex(RlnSession *session,
                             const char *path,
                             const char *text,
                             uint32_t offset,
                             RlnCompletionItems *out);

void rln_completion_items_free(RlnCompletionItems list);

/// The documentation of the completion item labelled `label` at `offset`:
/// what to show beside the selected item. Free with rln_documentation_free.
RlnStatus rln_completion_description(RlnSession *session,
                                     const char *path,
                                     const char *text,
                                     uint32_t offset,
                                     const char *label,
                                     RlnDocumentation *out);

/// Whether typing `typed` (a Unicode scalar value) into `text`, which leaves
/// the cursor at `offset` (UTF-16, after the character), should open the
/// completion list: a word's first letter, `.`, a space after `new` or
/// `override`, `#` at a line's start, `<` in a `///` comment. Syntax only.
RlnStatus rln_completion_trigger(RlnSession *session,
                                 const char *text,
                                 uint32_t offset,
                                 uint32_t typed,
                                 bool *out);

// MARK: - inlay hints, quick info

/// Bits of the `options` of rln_inlay_hints: Roslyn's inline hint check
/// boxes. rln_inlay_default_options() is what Roslyn shows once they are on.
enum {
    /// Parameter names at all.
    RLN_INLAY_PARAMETERS = 1 << 0,
    /// Before a literal: `Wait(500)`.
    RLN_INLAY_LITERAL_PARAMETERS = 1 << 1,
    /// Before a `new`.
    RLN_INLAY_OBJECT_CREATION_PARAMETERS = 1 << 2,
    /// Before anything else. Off by default, as in Roslyn.
    RLN_INLAY_OTHER_PARAMETERS = 1 << 3,
    /// Inside an indexer's `[...]`.
    RLN_INLAY_INDEXER_PARAMETERS = 1 << 4,
    /// Not for `Max(value1, value2)`.
    RLN_INLAY_SUPPRESS_DIFFERING_BY_SUFFIX = 1 << 5,
    /// Not for `SetColor(color)`.
    RLN_INLAY_SUPPRESS_MATCHING_METHOD_INTENT = 1 << 6,
    /// Not for `Load(path)`.
    RLN_INLAY_SUPPRESS_MATCHING_ARGUMENT_NAME = 1 << 7,
    /// Types at all.
    RLN_INLAY_TYPES = 1 << 8,
    /// For `var`, in declarations, `foreach`, `out var`, deconstruction.
    RLN_INLAY_IMPLICIT_VARIABLE_TYPES = 1 << 9,
    /// For a lambda's parameters that have no type written.
    RLN_INLAY_LAMBDA_PARAMETER_TYPES = 1 << 10,
    /// After the `new` of `new()`.
    RLN_INLAY_IMPLICIT_OBJECT_CREATION = 1 << 11,
};

/// Bits in RlnInlayHint.flags.
enum {
    RLN_INLAY_PADDING_LEFT = 1 << 0,
    RLN_INLAY_PADDING_RIGHT = 1 << 1,
    /// `target_*` say where clicking the hint goes.
    RLN_INLAY_HAS_TARGET = 1 << 2,
    /// `replace_*` say what double-clicking it writes.
    RLN_INLAY_HAS_REPLACEMENT = 1 << 3,
};

/// One inlay hint, in UTF-16 code units.
typedef struct RlnInlayHint {
    /// Drawn before the character here.
    uint32_t position;
    /// `count:` or `int`.
    RlnText label;
    /// The parameter's or type's declaration: relative to the project root,
    /// or an assembly's path.
    RlnText target_path;
    uint32_t target_line;
    uint32_t target_character;
    /// `replace_length` code units at `replace_start` of the file become
    /// `replace_text`: `count: ` inserted, or `var` made the type.
    uint32_t replace_start;
    uint32_t replace_length;
    RlnText replace_text;
    /// 0 a type, 1 a parameter name.
    uint8_t kind;
    /// RLN_INLAY_PADDING_LEFT and the rest.
    uint8_t flags;
} RlnInlayHint;

/// Free with rln_inlay_hints_free.
typedef struct RlnInlayHints {
    const RlnInlayHint *items;
    size_t count;
    const uint8_t *strings;
    size_t strings_length;
} RlnInlayHints;

/// The options Roslyn shows once inline hints are turned on.
uint32_t rln_inlay_default_options(void);

/// The inlay hints for `start..end` (UTF-16) of the file as the editor has
/// it — `text` as for rln_definition_in — as `options` (RLN_INLAY_* bits)
/// allow: parameter names before arguments, types after `var` and the
/// rest. Only the bodies in the range are bound; ask for what is on
/// screen. Needs a compilation. Free with rln_inlay_hints_free.
RlnStatus rln_inlay_hints(RlnSession *session,
                          const char *path,
                          const char *text,
                          uint32_t start,
                          uint32_t end,
                          uint32_t options,
                          RlnInlayHints *out);

void rln_inlay_hints_free(RlnInlayHints hints);

/// Roslyn's quick info: the symbol written out, its documentation, what
/// its type parameters are here and what a lambda captures. Every text is a
/// slice of `strings`; an empty one is a section that is not there.
typedef struct RlnQuickInfo {
    /// What it is about, UTF-16.
    uint32_t start;
    uint32_t length;
    /// `(local variable) int count`, `(property) int List<T>.Count { get; }`.
    RlnText description;
    RlnText summary;
    RlnText returns;
    /// A property's `<value>`.
    RlnText value;
    RlnText remarks;
    /// The value known at compile time: `10`, `"count"`.
    RlnText constant;
    /// Newline-separated: the exception types the comment names.
    RlnText exceptions;
    /// Newline-separated: `T is int`.
    RlnText type_parameters;
    /// Newline-separated: what a lambda or local function captures.
    RlnText captures;
    const RlnDocParameter *parameters;
    size_t parameter_count;
    const uint8_t *strings;
    size_t strings_length;
} RlnQuickInfo;

/// The quick info for `offset` (UTF-16): on a name, a `var`, a type
/// keyword, `this`, `nameof`, a `new()`, a lambda's `=>` or an operator
/// that calls a user-defined one. RLN_NOT_A_NAME where there is nothing to
/// say. Needs a compilation. Free with rln_quick_info_free.
RlnStatus rln_quick_info(RlnSession *session,
                         const char *path,
                         const char *text,
                         uint32_t offset,
                         RlnQuickInfo *out);

void rln_quick_info_free(RlnQuickInfo info);

// MARK: - .editorconfig, fix all, completion filtering

/// One .editorconfig setting: the key, lowercased, and its value as
/// written. Both are slices of the list's `strings`.
typedef struct RlnSetting {
    RlnText key;
    RlnText value;
} RlnSetting;

/// Free with rln_settings_free.
typedef struct RlnSettings {
    const RlnSetting *items;
    size_t count;
    const uint8_t *strings;
    size_t strings_length;
} RlnSettings;

/// Every .editorconfig setting that applies to `path`, keys sorted: what
/// the files from its directory up to a `root = true` one say, nearer ones
/// winning. The session already applies them — to formatting, diagnostic
/// severities, code style and naming — so this is for an editor's own use:
/// its tab width, say. Needs no compilation. Free with rln_settings_free.
RlnStatus rln_editorconfig(RlnSession *session, const char *path, RlnSettings *out);

void rln_settings_free(RlnSettings settings);

/// The `scope` of rln_fix_all.
#define RLN_FIX_ALL_DOCUMENT 0
#define RLN_FIX_ALL_PROJECT 1

/// Fix All: the fix for diagnostic `code` — `CS0246`, `CS0168`, `IDE0005`,
/// `IDE0051`, `IDE1006`, … — applied to every occurrence of it in the file
/// (`text` as for rln_definition_in) or, with RLN_FIX_ALL_PROJECT, in the
/// whole project, as one set of edits. Needs a compilation. Free with
/// rln_edits_free.
RlnStatus rln_fix_all(RlnSession *session,
                      const char *path,
                      const char *text,
                      const char *code,
                      uint8_t scope,
                      RlnEdits *out);

/// A completion item that matched what was typed.
typedef struct RlnFilteredItem {
    /// Its position among the names given.
    uint32_t index;
    /// An RlnMatchKind.
    uint8_t kind;
    /// 1 when every letter matched in the case it was typed in.
    uint8_t case_sensitive;
} RlnFilteredItem;

/// Free with rln_filtered_items_free.
typedef struct RlnFilteredItems {
    const RlnFilteredItem *items;
    size_t count;
} RlnFilteredItems;

/// Filters and orders `count` completion names — each item's filter text,
/// or its label — by what has been `typed`, as Roslyn's pattern matcher
/// does: exact, prefix, word starts and camel humps (`GTD` for
/// GoToDefinition), substrings, near misses; letters in the typed case
/// first. Items that do not match are left out; nothing typed keeps them
/// all. Needs no session. Free with rln_filtered_items_free.
RlnStatus rln_completion_filter(const char *const *names,
                                size_t count,
                                const char *typed,
                                RlnFilteredItems *out);

void rln_filtered_items_free(RlnFilteredItems items);

// MARK: - refactoring dialogs: change signature, extract interface and base class, pull up, overrides, move statics

/// One parameter of a changed signature: `existing` is the index of a
/// parameter there now, or negative for a new one described by the rest.
typedef struct RlnChangeParam {
    int32_t existing;
    const char *type_name;
    const char *name;
    /// NULL for a required parameter.
    const char *default_value;
    /// What existing calls pass; NULL leaves an optional one out (and passes
    /// `default` for a required one).
    const char *call_site;
} RlnChangeParam;

/// A member chosen in a dialog, and whether it stays behind as an override
/// of a new abstract member instead of moving.
typedef struct RlnMemberChoice {
    const char *name;
    uint8_t make_abstract;
} RlnMemberChoice;

/// A dialog's refactoring: its edits (new files are edits to paths that do
/// not exist yet), or why there are none — which is RLN_OK, with the reason
/// in `refused`, a slice of `edits.strings`. Free with
/// rln_refactor_result_free, not rln_edits_free.
typedef struct RlnRefactorResult {
    RlnEdits edits;
    RlnText refused;
} RlnRefactorResult;

/// One parameter as the change-signature dialog lists it.
typedef struct RlnSignatureParameter {
    /// `ref `, `out `, `in `, `this `, `params ` or empty.
    RlnText modifier;
    RlnText type_name;
    RlnText name;
    RlnText default_value;
    uint8_t has_default;
} RlnSignatureParameter;

/// What the change-signature dialog shows. Free with rln_signature_info_free.
typedef struct RlnSignatureInfo {
    /// The member as one line: `Shop.Buy(string item, int count)`.
    RlnText display;
    /// Why the signature cannot change; empty when it can.
    RlnText refused;
    const RlnSignatureParameter *parameters;
    size_t parameter_count;
    const uint8_t *strings;
    size_t strings_length;
    /// Whether the first parameter cannot move: an extension's `this`.
    uint8_t first_is_fixed;
} RlnSignatureInfo;

/// Which dialog rln_dialog_members is asked for.
typedef enum RlnDialogKind {
    RLN_DIALOG_EXTRACT_INTERFACE = 0,
    RLN_DIALOG_EXTRACT_BASE_CLASS,
    RLN_DIALOG_PULL_MEMBERS_UP,
    RLN_DIALOG_GENERATE_OVERRIDES,
    RLN_DIALOG_MOVE_STATIC_MEMBERS,
} RlnDialogKind;

/// One line of a dialog's member list.
typedef struct RlnDialogMember {
    /// What to hand back to choose it.
    RlnText name;
    /// Its signature, as the list shows it.
    RlnText display;
    uint8_t selected;
} RlnDialogMember;

/// What a dialog lists. Free with rln_dialog_members_free.
typedef struct RlnDialogMembers {
    RlnText type_name;
    /// The name suggested for the new type; empty when none is made.
    RlnText suggested_name;
    /// Where the members can go, one per line: pull members up's base types.
    RlnText destinations;
    /// Why there is nothing to list; empty otherwise.
    RlnText refused;
    const RlnDialogMember *members;
    size_t member_count;
    const uint8_t *strings;
    size_t strings_length;
} RlnDialogMembers;

/// The method or constructor at `offset` (UTF-16), or a call of it, and its
/// parameters. One whose signature cannot change is RLN_OK with the reason in
/// `refused`. Needs a compilation.
RlnStatus rln_signature_info(RlnSession *session,
                             const char *path,
                             const char *text,
                             uint32_t offset,
                             RlnSignatureInfo *out);

void rln_signature_info_free(RlnSignatureInfo info);

/// What the dialog of `kind` (an RlnDialogKind) lists for the type at
/// `offset`, with the entries that start ticked and a suggested name.
RlnStatus rln_dialog_members(RlnSession *session,
                             const char *path,
                             const char *text,
                             uint32_t offset,
                             uint32_t kind,
                             RlnDialogMembers *out);

void rln_dialog_members_free(RlnDialogMembers members);

/// Changes the signature at `offset` to the `count` parameters of `params`:
/// the declaration, its overrides and implementations, their documentation,
/// and every call across the project.
RlnStatus rln_change_signature(RlnSession *session,
                               const char *path,
                               const char *text,
                               uint32_t offset,
                               const RlnChangeParam *params,
                               size_t count,
                               RlnRefactorResult *out);

/// Extracts an interface called `name` declaring the `count` members named
/// in `members` (every overload of each) from the type at `offset`, into a
/// file of its own when `new_file` is set, above the type otherwise.
RlnStatus rln_extract_interface(RlnSession *session,
                                const char *path,
                                const char *text,
                                uint32_t offset,
                                const char *name,
                                const char *const *members,
                                size_t count,
                                uint8_t new_file,
                                RlnRefactorResult *out);

/// Extracts a base class called `name` from the class at `offset`, moving
/// the chosen members into it or declaring them abstract there.
RlnStatus rln_extract_base_class(RlnSession *session,
                                 const char *path,
                                 const char *text,
                                 uint32_t offset,
                                 const char *name,
                                 const RlnMemberChoice *members,
                                 size_t count,
                                 uint8_t new_file,
                                 RlnRefactorResult *out);

/// Pulls the chosen members of the type at `offset` up to its base class or
/// interface called `destination`.
RlnStatus rln_pull_members_up(RlnSession *session,
                              const char *path,
                              const char *text,
                              uint32_t offset,
                              const char *destination,
                              const RlnMemberChoice *members,
                              size_t count,
                              RlnRefactorResult *out);

/// Overrides the `count` inherited members of `members` — as
/// rln_dialog_members lists them, or by name — in the type at `offset`.
RlnStatus rln_generate_overrides(RlnSession *session,
                                 const char *path,
                                 const char *text,
                                 uint32_t offset,
                                 const char *const *members,
                                 size_t count,
                                 RlnRefactorResult *out);

/// Moves the `count` static members named in `members` of the type at
/// `offset` to the type called `destination`, with every use of them. A
/// destination the project does not have is made a static class, in a file
/// of its own when `new_file` is set.
RlnStatus rln_move_static_members(RlnSession *session,
                                  const char *path,
                                  const char *text,
                                  uint32_t offset,
                                  const char *destination,
                                  const char *const *members,
                                  size_t count,
                                  uint8_t new_file,
                                  RlnRefactorResult *out);

void rln_refactor_result_free(RlnRefactorResult result);

// MARK: - layer 5: code with no source

/// An assembly's types and members, written as C#, from its metadata. No
/// method bodies: the metadata holds IL, and one body at a time is what
/// rln_method_body is for. Free the text with rln_text_free.
RlnStatus rln_assembly_text(RlnSession *session, const char *path, RlnString *out);

/// The metadata token of the member declared on `line` of that text, or zero
/// when there is none — which most lines have, and which is not an error.
uint32_t rln_assembly_token_at_line(RlnSession *session, const char *path, uint32_t line);

/// One method's IL, with its metadata tokens resolved to names. Free the text
/// with rln_text_free.
RlnStatus rln_method_body(RlnSession *session,
                          const char *path,
                          uint32_t token,
                          RlnString *out);

// MARK: - checking this header against the library

/// The number of RlnDeclarationKind values this library knows. Compare it
/// against your own table at startup: a mismatch means this header and the
/// library it linked against have drifted apart.
uint32_t rln_declaration_kind_count(void);

/// The same for RlnClass.
uint32_t rln_class_count(void);

/// The same for RlnCompletionKind.
uint32_t rln_completion_kind_count(void);

/// The same for RlnActionKind.
uint32_t rln_action_kind_count(void);

#ifdef __cplusplus
}
#endif


// MARK: - hot reload

/// Starts hot reload for a Unity project: every source generator over
/// Assembly-CSharp, the project compiled with what they wrote, and the
/// Assembly-CSharp an editor is to load built. `tools` is JSON {"dotnet",
/// "gend", "minigen", "runtime"}; `paths` as for rln_compile. Blocks for tens
/// of seconds. Answers JSON {"ok":true,"assembly","milliseconds","stubs"} or
/// {"ok":false,"error"}. Free with rln_text_free.
RlnString rln_hot_start(RlnSession *session,
                        const char *tools,
                        const char *const *paths,
                        size_t count);

/// What saving `saved` comes to under hot reload: JSON with "kind" —
/// "patch" ("assembly" for the editor's probe, "methods"), "unchanged",
/// "broken" ("reason"), "reload" ("reason"), "outside", "error" — and
/// "milliseconds". Free with rln_text_free.
RlnString rln_hot_save(RlnSession *session,
                       const char *const *saved,
                       size_t saved_count,
                       const char *const *paths,
                       size_t count);

/// The text of a file as the build the editor runs has it, as JSON
/// {"text": ...}, or {} where that build does not have the file.
RlnString rln_hot_base_text(RlnSession *session, const char *const *path);

/// A whole build of the files as they are, for the editor to reload on.
/// Answers as rln_hot_start.
RlnString rln_hot_rebuild(RlnSession *session,
                          const char *const *paths,
                          size_t count);

#endif // RUSTLYN_H
