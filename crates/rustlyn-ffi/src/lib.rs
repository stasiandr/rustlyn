//! The C ABI over [`rustlyn_ide`], for an editor that is not written in Rust.
//!
//! Everything interesting is a layer below this. What is here is the
//! boundary, and a boundary has exactly three jobs: hand ownership across it
//! without losing track of who frees what, never let a panic cross it, and
//! never trust anything coming the other way.
//!
//! **Results are one allocation, not one per string.** Anything with a list
//! in it comes back as a struct of arrays beside a single UTF-8 blob, and the
//! items hold offsets into that blob rather than pointers. A file with two
//! thousand declarations is then two allocations and one free, instead of
//! twenty thousand of each — and the caller reads a name by slicing bytes it
//! already has, which is what an editor wanted to do with it anyway.
//!
//! **Every result is freed by the function named for it.** A result allocated
//! by Rust must be freed by Rust: the two sides have different allocators,
//! and handing a Rust pointer to `free` is undefined behaviour that works
//! most of the time, which is the worst kind.
//!
//! **A panic never crosses.** Unwinding into C is undefined behaviour, so
//! every entry point catches. A panic here is a bug in the layers below, and
//! the honest thing to do with one is to report a failure and leave the
//! caller running.
//!
//! # Safety
//!
//! Every function here is `unsafe` in the sense that matters even where the
//! signature does not say so: it takes pointers it cannot check. The contract
//! is the usual one, and it is the caller's to keep:
//!
//! * A `const char *` is NUL-terminated and valid UTF-8, or null where the
//!   documentation says null is allowed.
//! * A session pointer came from `rln_session_new` and has not been freed.
//! * A result pointer came from the call named in its type and is freed once,
//!   by the matching free function.
//! * A session may be used from several threads at once. A result may not be
//!   freed from two.

#![allow(clippy::missing_safety_doc)] // the module documentation states it once

use std::ffi::{CStr, c_char};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::PathBuf;
use std::sync::Mutex;

use rustlyn_ide::outline::DeclarationKind;
use rustlyn_ide::project::ProjectKind;
use rustlyn_ide::semantic::CompletionKind;
use rustlyn_ide::session::{Location, Refusal, Session};

// MARK: - syntax-level editing: formatting, structure, braces, comments
mod editing;
pub use editing::*;

// MARK: - refactoring dialogs: change signature, extract interface and base class, pull up, overrides, move statics
mod refactor;
pub use refactor::*;

/// How a call went.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(C)]
pub enum RlnStatus {
    Ok = 0,
    /// The file is not open.
    NotOpen = 1,
    /// The file is not C#.
    NotCsharp = 2,
    /// The project has not been indexed yet.
    NotIndexed = 3,
    /// The cursor is not on a name.
    NotAName = 4,
    /// The receiver of a member access could not be typed.
    ReceiverUnknown = 5,
    /// The name is not declared in this project.
    NotInProject = 6,
    /// The assembly could not be read.
    Assembly = 7,
    /// The file could not be read.
    Io = 8,
    /// A pointer was null, or a string was not UTF-8. A bug in the caller.
    BadArgument = 9,
    /// Something below panicked. A bug in the layers underneath.
    Panicked = 10,
    /// The project has not been compiled yet.
    NotCompiled = 11,
    /// The caller called it off before it finished.
    Cancelled = 12,
}

impl From<&Refusal> for RlnStatus {
    fn from(refusal: &Refusal) -> Self {
        match refusal {
            Refusal::NotOpen => Self::NotOpen,
            Refusal::NotCsharp => Self::NotCsharp,
            Refusal::NotIndexed => Self::NotIndexed,
            Refusal::NotCompiled => Self::NotCompiled,
            Refusal::NotAName => Self::NotAName,
            Refusal::ReceiverUnknown(_) => Self::ReceiverUnknown,
            Refusal::NotInProject(_) => Self::NotInProject,
            Refusal::Assembly(_) => Self::Assembly,
            Refusal::Io(_) => Self::Io,
            Refusal::Cancelled => Self::Cancelled,
        }
    }
}

/// A session, and the last thing that went wrong in it.
///
/// The message is kept here rather than returned, because a caller that only
/// wants the status should not have to free a string to get it. It belongs to
/// the session, so two threads asking at once would race — hence the lock,
/// and hence `rln_last_error` copying rather than lending.
#[derive(Debug)]
pub struct RlnSession {
    session: Session,
    last_error: Mutex<String>,
}

impl RlnSession {
    fn note(&self, refusal: &Refusal) -> RlnStatus {
        *self
            .last_error
            .lock()
            .unwrap_or_else(|error| error.into_inner()) = refusal.to_string();
        RlnStatus::from(refusal)
    }
}

/// A coloured run, in UTF-16 code units.
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct RlnRun {
    pub start: u32,
    pub length: u32,
    /// A `rustlyn_ide::Class`, as its discriminant.
    pub class: u8,
}

/// A list of runs. Freed with `rln_runs_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnRuns {
    pub items: *const RlnRun,
    pub count: usize,
}

/// A slice of the string blob that comes with a result.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnText {
    pub offset: u32,
    pub length: u32,
}

/// One declaration of a file's outline.
///
/// Every string is an offset into the outline's `strings` blob. The lists —
/// bases, attributes, parameter types — are stretches of that blob holding
/// their items separated by a single `\n`, which no name or type contains.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnDeclaration {
    pub name: RlnText,
    pub container: RlnText,
    pub type_text: RlnText,
    pub keyword: RlnText,
    /// Newline-separated.
    pub bases: RlnText,
    pub type_parameters: RlnText,
    pub attributes: RlnText,
    /// Newline-separated, each `type name`.
    pub parameters: RlnText,
    /// The name's span, in UTF-16 code units from the start of the file.
    pub name_start: u32,
    pub name_length: u32,
    /// The whole declaration, for folding.
    pub full_start: u32,
    pub full_length: u32,
    pub line: u32,
    pub depth: u32,
    /// A `DeclarationKind`, as its discriminant.
    pub kind: u8,
    /// Bit 0 static, 1 abstract, 2 override, 3 partial, 4 extension method.
    pub flags: u8,
    pub parameter_count: u16,
}

/// A file's outline. Freed with `rln_outline_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnOutline {
    pub declarations: *const RlnDeclaration,
    pub count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
    /// Newline-separated: the namespaces the file declares.
    pub namespaces: RlnText,
    /// Newline-separated: each `using`, aliases written as `alias=name`.
    pub usings: RlnText,
    pub parse_errors: u32,
}

/// Somewhere to go.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnLocation {
    /// Relative to the project root.
    pub path: RlnText,
    pub name: RlnText,
    pub line: u32,
    /// UTF-16 code units from the start of the line.
    pub character: u32,
    pub length: u32,
    pub kind: u8,
}

/// The answer to `⌘B`. Freed with `rln_locations_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnLocations {
    pub items: *const RlnLocation,
    pub count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
    /// The word that was under the cursor.
    pub word: RlnText,
    /// Whether the scope settled it. When false the caller should offer the
    /// list rather than jump to the first of it.
    pub certain: bool,
}

/// Text owned by Rust. Freed with `rln_text_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnString {
    pub bytes: *const u8,
    pub length: usize,
}

/// What a reindex did.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnReport {
    pub files: usize,
    pub reused: usize,
    pub parsed: usize,
    pub unreadable: usize,
}

/// What the cache has been doing.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnStatistics {
    pub stamped: u64,
    pub rehashed: u64,
    pub from_disk: u64,
    pub computed: u64,
    pub entries: usize,
    pub bytes: usize,
}

/// What compiling the project did.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnCompiled {
    pub files: usize,
    pub references: usize,
    /// How many `.csproj` files described the project; zero when it was
    /// worked out without any.
    pub projects: usize,
    pub milliseconds: u64,
    /// 0 from project files, 1 a Unity project without them, 2 a folder.
    pub kind: u8,
    /// Nothing had changed, so the compilation there was kept.
    pub unchanged: bool,
}

/// One completion.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnCompletion {
    pub label: RlnText,
    /// The type or signature, to show beside the label.
    pub detail: RlnText,
    /// A `CompletionKind`, as its discriminant.
    pub kind: u8,
    /// Lower sorts first.
    pub rank: u8,
}

/// A completion list. Freed with `rln_completions_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnCompletions {
    pub items: *const RlnCompletion,
    pub count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
    /// Where the word being completed starts, in UTF-16 code units.
    pub start: u32,
}

/// A stretch of UTF-16 code units.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnRange {
    pub start: u32,
    pub end: u32,
}

/// Ranges. Freed with `rln_ranges_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnRanges {
    pub items: *const RlnRange,
    pub count: usize,
}

/// Something wrong in a file.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnDiagnostic {
    /// UTF-16 offset and length.
    pub start: u32,
    pub length: u32,
    /// 1 info, 2 warning, 3 error; 0 hidden, which only comes with the
    /// unnecessary tag: code to draw faded, not to list.
    pub severity: u8,
    /// Bit 0: unnecessary, draw faded. Bit 1: deprecated, strike through.
    /// In what was padding before it, so the layout is as it was.
    pub tags: u8,
    pub code: RlnText,
    pub message: RlnText,
}

/// A file's diagnostics. Freed with `rln_diagnostics_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnDiagnostics {
    pub items: *const RlnDiagnostic,
    pub count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
    /// The compiler looked, not only the parser.
    pub semantic: bool,
}

/// One overload: its label, and its parameters as ranges of the label.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnSignature {
    pub label: RlnText,
    /// Index of its first parameter in `parameters`.
    pub first_parameter: u32,
    pub parameter_count: u32,
}

/// The overloads of the call being typed. Freed with `rln_signatures_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnSignatures {
    pub items: *const RlnSignature,
    pub count: usize,
    /// UTF-16 ranges into each label.
    pub parameters: *const RlnRange,
    pub parameter_count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
    pub active: u32,
    pub parameter: u32,
}

/// A documented parameter.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnDocParameter {
    pub name: RlnText,
    pub text: RlnText,
}

/// What a name's documentation says. Freed with `rln_documentation_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnDocumentation {
    pub signature: RlnText,
    pub container: RlnText,
    pub summary: RlnText,
    pub returns: RlnText,
    pub parameters: *const RlnDocParameter,
    pub parameter_count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
}

/// One replacement: `length` UTF-16 code units at `start` of `path` become
/// `text`.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnEdit {
    /// Absolute.
    pub path: RlnText,
    pub text: RlnText,
    pub start: u32,
    pub length: u32,
}

/// A file to rename, for a type whose file follows its name.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnRename {
    pub from: RlnText,
    pub to: RlnText,
}

/// Edits across the project. Within a file they are in order and never
/// overlap: apply them from the last to the first. Freed with
/// `rln_edits_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnEdits {
    pub items: *const RlnEdit,
    pub count: usize,
    pub renames: *const RlnRename,
    pub rename_count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
}

/// One entry of the light bulb, and the stretch of the shared edit and
/// rename arrays that is what it does.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnCodeAction {
    pub title: RlnText,
    /// The diagnostic code it fixes; empty for a refactoring.
    pub fixes: RlnText,
    pub first_edit: u32,
    pub edit_count: u32,
    pub first_rename: u32,
    pub rename_count: u32,
    /// An `ActionKind`, as its discriminant.
    pub kind: u8,
}

/// The light bulb. Freed with `rln_code_actions_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnCodeActions {
    pub items: *const RlnCodeAction,
    pub count: usize,
    pub edits: *const RlnEdit,
    pub edit_count: usize,
    pub renames: *const RlnRename,
    pub rename_count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
}

// MARK: - the boundary itself

/// Runs `body`, turning a panic into a status instead of letting it cross.
///
/// What a request reads is a syntax tree or a bound one, and walking either
/// recurses as deep as the tree is, which the parser lets be twelve thousand
/// levels: more than the eight megabytes of a main thread hold, in an
/// unoptimized build, and more than the editor's own thread may have. The
/// work is done on a stack that size, which costs a thread for the request
/// and nothing where the caller is on one already.
fn guard<T>(fallback: T, body: impl FnOnce() -> T) -> T {
    /// Moved to the thread that does the work. The pointers a request holds
    /// belong to the caller, who is waiting for the answer, and nothing else
    /// has them until it is given.
    struct Handoff<T>(T);
    // SAFETY: the caller is blocked until the work is done, as `deep` waits
    // for it, so nothing is used from two threads at once.
    unsafe impl<T> Send for Handoff<T> {}
    impl<T> Handoff<T> {
        fn into_inner(self) -> T {
            self.0
        }
    }
    let work = Handoff((fallback, body));
    rustlyn_ide::deep(move || {
        let (fallback, body) = work.into_inner();
        Handoff(shallow(fallback, body))
    })
    .into_inner()
}

/// [`guard`] for what reads no tree: a pointer handed back, a count, a
/// session made or dropped. A thread for each would be most of the cost.
fn shallow<T>(fallback: T, body: impl FnOnce() -> T) -> T {
    catch_unwind(AssertUnwindSafe(body)).unwrap_or(fallback)
}

/// Borrows a C string as a `&str`, or `None` when it is null or not UTF-8.
unsafe fn borrow<'a>(pointer: *const c_char) -> Option<&'a str> {
    if pointer.is_null() {
        return None;
    }
    unsafe { CStr::from_ptr(pointer) }.to_str().ok()
}

unsafe fn held<'a>(pointer: *mut RlnSession) -> Option<&'a RlnSession> {
    if pointer.is_null() {
        return None;
    }
    Some(unsafe { &*pointer })
}

/// Hands a vector to C, and forgets it. The matching free takes it back.
fn leak<T>(mut items: Vec<T>) -> (*const T, usize) {
    items.shrink_to_fit();
    let count = items.len();
    let pointer = items.as_ptr();
    std::mem::forget(items);
    (pointer, count)
}

/// Takes back what `leak` handed out.
unsafe fn reclaim<T>(pointer: *const T, count: usize) {
    if pointer.is_null() || count == 0 {
        // A zero-length vector's pointer is dangling but not null, and
        // reclaiming it with a count of zero is what `Vec` itself does.
        return;
    }
    drop(unsafe { Vec::from_raw_parts(pointer.cast_mut(), count, count) });
}

/// Collects strings into one blob, handing out slices of it.
#[derive(Default)]
struct Strings {
    bytes: Vec<u8>,
}

impl Strings {
    fn add(&mut self, text: &str) -> RlnText {
        let offset = self.bytes.len() as u32;
        self.bytes.extend_from_slice(text.as_bytes());
        RlnText {
            offset,
            length: text.len() as u32,
        }
    }

    /// A list, separated by newlines — which no identifier or type name
    /// contains, so the caller can split on them without escaping anything.
    fn add_list<S: AsRef<str>>(&mut self, items: &[S]) -> RlnText {
        let offset = self.bytes.len() as u32;
        for (index, item) in items.iter().enumerate() {
            if index > 0 {
                self.bytes.push(b'\n');
            }
            self.bytes.extend_from_slice(item.as_ref().as_bytes());
        }
        RlnText {
            offset,
            length: self.bytes.len() as u32 - offset,
        }
    }
}

// MARK: - a session

/// Opens a session over `root`.
///
/// `cache_directory` may be null, in which case nothing is kept between runs.
/// `symbols` is `symbol_count` preprocessor symbols, and may be null when
/// there are none.
///
/// Returns null when an argument is null or not UTF-8.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_session_new(
    root: *const c_char,
    cache_directory: *const c_char,
    symbols: *const *const c_char,
    symbol_count: usize,
) -> *mut RlnSession {
    shallow(std::ptr::null_mut(), || {
        let Some(root) = (unsafe { borrow(root) }) else {
            return std::ptr::null_mut();
        };
        let cache = unsafe { borrow(cache_directory) }.map(PathBuf::from);
        let mut defined = Vec::new();
        if !symbols.is_null() {
            for index in 0..symbol_count {
                if let Some(symbol) = unsafe { borrow(*symbols.add(index)) } {
                    defined.push(symbol.to_owned());
                }
            }
        }
        Box::into_raw(Box::new(RlnSession {
            session: Session::new(root, cache, defined),
            last_error: Mutex::new(String::new()),
        }))
    })
}

/// Keeps decompiled assemblies in `directory`, shared by every session
/// given the same one, rather than in the project's cache. Call once, before
/// the first assembly is asked for; `RLN_BAD_ARGUMENT` for a null argument
/// or when it was set already.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_session_share_assembly_cache(
    session: *mut RlnSession,
    directory: *const c_char,
) -> RlnStatus {
    shallow(RlnStatus::Panicked, || {
        let (Some(session), Some(directory)) =
            (unsafe { held(session) }, unsafe { borrow(directory) })
        else {
            return RlnStatus::BadArgument;
        };
        if session
            .session
            .share_assembly_cache(PathBuf::from(directory))
        {
            RlnStatus::Ok
        } else {
            RlnStatus::BadArgument
        }
    })
}

/// Closes a session. Null is allowed and does nothing.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_session_free(session: *mut RlnSession) {
    if session.is_null() {
        return;
    }
    // What the session kept of bound bodies is dropped level by level, as
    // deep as the bodies were: on the stack made for them.
    guard((), || drop(unsafe { Box::from_raw(session) }));
}

/// Copies the message from the last failure in this session.
///
/// Freed with `rln_text_free`. Empty when nothing has failed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_last_error(session: *mut RlnSession) -> RlnString {
    shallow(
        RlnString {
            bytes: std::ptr::null(),
            length: 0,
        },
        || {
            let Some(session) = (unsafe { held(session) }) else {
                return RlnString {
                    bytes: std::ptr::null(),
                    length: 0,
                };
            };
            let message = session
                .last_error
                .lock()
                .unwrap_or_else(|error| error.into_inner())
                .clone();
            let (bytes, length) = leak(message.into_bytes());
            RlnString { bytes, length }
        },
    )
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_text_free(text: RlnString) {
    shallow((), || unsafe { reclaim(text.bytes, text.length) });
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_statistics(session: *mut RlnSession) -> RlnStatistics {
    shallow(RlnStatistics::default(), || {
        let Some(session) = (unsafe { held(session) }) else {
            return RlnStatistics::default();
        };
        let statistics = session.session.statistics();
        RlnStatistics {
            stamped: statistics.stamped,
            rehashed: statistics.rehashed,
            from_disk: statistics.from_disk,
            computed: statistics.computed,
            entries: statistics.entries,
            bytes: statistics.bytes,
        }
    })
}

// MARK: - layer 1

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_open(session: *mut RlnSession, path: *const c_char) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path)) = (unsafe { held(session) }, unsafe { borrow(path) })
        else {
            return RlnStatus::BadArgument;
        };
        match session.session.open(path) {
            Ok(_) => RlnStatus::Ok,
            Err(refusal) => session.note(&refusal),
        }
    })
}

/// Opens a buffer the editor already holds the text of.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_open_text(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Some(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                borrow(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        session.session.open_text(path, text);
        RlnStatus::Ok
    })
}

/// Replaces an open file's text.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_set_text(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Some(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                borrow(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        match session.session.set_text(path, text) {
            Ok(_) => RlnStatus::Ok,
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_close(session: *mut RlnSession, path: *const c_char) {
    shallow((), || {
        if let (Some(session), Some(path)) = (unsafe { held(session) }, unsafe { borrow(path) }) {
            session.session.close(path);
        }
    });
}

// MARK: - layer 2

/// Colours lines `first` through `last` of an open file.
///
/// `out` is filled on success and left alone otherwise. Free it with
/// `rln_runs_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_classify(
    session: *mut RlnSession,
    path: *const c_char,
    first: u32,
    last: u32,
    out: *mut RlnRuns,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path)) = (unsafe { held(session) }, unsafe { borrow(path) })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.classify(path, first, last) {
            Ok(runs) => {
                let items: Vec<RlnRun> = runs
                    .into_iter()
                    .map(|run| RlnRun {
                        start: run.start,
                        length: run.length,
                        class: run.class as u8,
                    })
                    .collect();
                let (items, count) = leak(items);
                unsafe { out.write(RlnRuns { items, count }) };
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_runs_free(runs: RlnRuns) {
    shallow((), || unsafe { reclaim(runs.items, runs.count) });
}

/// Walks the whole of an open file so that a jump to any line is as cheap as
/// a scroll. For a background thread.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_warm(session: *mut RlnSession, path: *const c_char) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path)) = (unsafe { held(session) }, unsafe { borrow(path) })
        else {
            return RlnStatus::BadArgument;
        };
        match session.session.warm(path) {
            Ok(()) => RlnStatus::Ok,
            Err(refusal) => session.note(&refusal),
        }
    })
}

// MARK: - layer 3

/// The outline of an open file. Free it with `rln_outline_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_outline(
    session: *mut RlnSession,
    path: *const c_char,
    out: *mut RlnOutline,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path)) = (unsafe { held(session) }, unsafe { borrow(path) })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        let outline = match session.session.outline(path) {
            Ok(outline) => outline,
            Err(refusal) => return session.note(&refusal),
        };
        // The spans in an outline are byte offsets; the editor counts UTF-16.
        let Some(document) = session.session.document(path) else {
            return RlnStatus::NotOpen;
        };
        let map = document.utf16();

        let mut strings = Strings::default();
        let namespaces = strings.add_list(&outline.namespaces);
        let usings: Vec<String> = outline
            .usings
            .iter()
            .map(|using| match &using.alias {
                Some(alias) => format!("{alias}={}", using.name),
                None => using.name.clone(),
            })
            .collect();
        let usings = strings.add_list(&usings);

        let declarations: Vec<RlnDeclaration> = outline
            .declarations
            .iter()
            .map(|declaration| {
                let parameters: Vec<String> = declaration
                    .parameters
                    .iter()
                    .map(|parameter| format!("{} {}", parameter.type_text, parameter.name))
                    .collect();
                let (name_start, name_length) = map.span(declaration.name_span);
                let (full_start, full_length) = map.span(declaration.full_span);
                RlnDeclaration {
                    name: strings.add(&declaration.name),
                    container: strings.add(declaration.container.as_deref().unwrap_or("")),
                    type_text: strings.add(declaration.type_text.as_deref().unwrap_or("")),
                    keyword: strings.add(&declaration.keyword),
                    bases: strings.add_list(&declaration.bases),
                    type_parameters: strings.add_list(&declaration.type_parameters),
                    attributes: strings.add_list(&declaration.attributes),
                    parameters: strings.add_list(&parameters),
                    name_start,
                    name_length,
                    full_start,
                    full_length,
                    line: declaration.line,
                    depth: declaration.depth,
                    kind: declaration.kind as u8,
                    flags: u8::from(declaration.is_static)
                        | (u8::from(declaration.is_abstract) << 1)
                        | (u8::from(declaration.is_override) << 2)
                        | (u8::from(declaration.is_partial) << 3)
                        | (u8::from(declaration.is_extension_method()) << 4),
                    parameter_count: declaration.parameters.len() as u16,
                }
            })
            .collect();

        let (declarations, count) = leak(declarations);
        let (bytes, strings_length) = leak(strings.bytes);
        unsafe {
            out.write(RlnOutline {
                declarations,
                count,
                strings: bytes,
                strings_length,
                namespaces,
                usings,
                parse_errors: outline.parse_errors,
            });
        }
        RlnStatus::Ok
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_outline_free(outline: RlnOutline) {
    shallow((), || unsafe {
        reclaim(outline.declarations, outline.count);
        reclaim(outline.strings, outline.strings_length);
    });
}

// MARK: - layer 4

/// Builds the project index over `count` paths.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_reindex(
    session: *mut RlnSession,
    paths: *const *const c_char,
    count: usize,
    out: *mut RlnReport,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let Some(session) = (unsafe { held(session) }) else {
            return RlnStatus::BadArgument;
        };
        if paths.is_null() && count > 0 {
            return RlnStatus::BadArgument;
        }
        let mut list = Vec::with_capacity(count);
        for index in 0..count {
            match unsafe { borrow(*paths.add(index)) } {
                Some(path) => list.push(PathBuf::from(path)),
                None => return RlnStatus::BadArgument,
            }
        }
        let report = session.session.reindex(&list);
        if !out.is_null() {
            unsafe {
                out.write(RlnReport {
                    files: report.files,
                    reused: report.reused,
                    parsed: report.parsed,
                    unreadable: report.unreadable,
                });
            }
        }
        RlnStatus::Ok
    })
}

/// Where the name at `offset` was declared. `offset` is in UTF-16 code units.
///
/// Free the result with `rln_locations_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_definition(
    session: *mut RlnSession,
    path: *const c_char,
    offset: u32,
    out: *mut RlnLocations,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path)) = (unsafe { held(session) }, unsafe { borrow(path) })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.definition(path, offset) {
            Ok(definition) => {
                let mut strings = Strings::default();
                let word = strings.add(&definition.word);
                let items = pack_locations(&definition.targets, &mut strings);
                let (items, count) = leak(items);
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnLocations {
                        items,
                        count,
                        strings: bytes,
                        strings_length,
                        word,
                        certain: definition.certain,
                    });
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

/// What derives from, or overrides, whatever is at `offset`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_implementations(
    session: *mut RlnSession,
    path: *const c_char,
    offset: u32,
    out: *mut RlnLocations,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path)) = (unsafe { held(session) }, unsafe { borrow(path) })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.implementations(path, offset) {
            Ok(locations) => {
                let mut strings = Strings::default();
                let word = strings.add("");
                let items = pack_locations(&locations, &mut strings);
                let (items, count) = leak(items);
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnLocations {
                        items,
                        count,
                        strings: bytes,
                        strings_length,
                        word,
                        certain: true,
                    });
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

fn pack_locations(locations: &[Location], strings: &mut Strings) -> Vec<RlnLocation> {
    locations
        .iter()
        .map(|location| RlnLocation {
            path: strings.add(&location.path.to_string_lossy()),
            name: strings.add(&location.name),
            line: location.line,
            character: location.character,
            length: location.length,
            kind: location.kind as u8,
        })
        .collect()
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_locations_free(locations: RlnLocations) {
    shallow((), || unsafe {
        reclaim(locations.items, locations.count);
        reclaim(locations.strings, locations.strings_length);
    });
}

// MARK: - layer 6

/// Compiles the project over `count` paths, or over the index's files when
/// `count` is zero. Blocks for as long as declaring the project takes; `out`
/// may be null.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_compile(
    session: *mut RlnSession,
    paths: *const *const c_char,
    count: usize,
    out: *mut RlnCompiled,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let Some(session) = (unsafe { held(session) }) else {
            return RlnStatus::BadArgument;
        };
        let Some(list) = (unsafe { path_list(paths, count) }) else {
            return RlnStatus::BadArgument;
        };
        let compiled = session.session.compile(&list);
        if !out.is_null() {
            unsafe {
                out.write(RlnCompiled {
                    files: compiled.files,
                    references: compiled.references,
                    projects: compiled.projects,
                    milliseconds: compiled.milliseconds,
                    kind: kind_code(compiled.kind),
                    unchanged: compiled.unchanged,
                });
            }
        }
        RlnStatus::Ok
    })
}

const fn kind_code(kind: ProjectKind) -> u8 {
    match kind {
        ProjectKind::Msbuild => 0,
        ProjectKind::Unity => 1,
        ProjectKind::Folder => 2,
    }
}

/// Writes the compilation to the session's cache directory, if it changed
/// since it was last written or read. For when the project closes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_save_compilation(session: *mut RlnSession) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let Some(session) = (unsafe { held(session) }) else {
            return RlnStatus::BadArgument;
        };
        match session.session.save_compilation() {
            Ok(_) => RlnStatus::Ok,
            Err(error) => session.note(&Refusal::Io(error.to_string())),
        }
    })
}

/// Reads back the compilation the last run wrote and installs it, so the
/// compiler answers before compiling. `RLN_NOT_COMPILED` when there is none
/// to read. `out` may be null.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_load_compilation(
    session: *mut RlnSession,
    out: *mut RlnCompiled,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let Some(session) = (unsafe { held(session) }) else {
            return RlnStatus::BadArgument;
        };
        let Some(loaded) = session.session.load_compilation() else {
            return RlnStatus::NotCompiled;
        };
        if !out.is_null() {
            unsafe {
                out.write(RlnCompiled {
                    files: loaded.files,
                    references: loaded.references,
                    projects: loaded.projects,
                    milliseconds: loaded.milliseconds,
                    kind: kind_code(loaded.kind),
                    unchanged: true,
                });
            }
        }
        RlnStatus::Ok
    })
}

/// `count` C strings as paths, or `None` when one of them is bad.
unsafe fn path_list(paths: *const *const c_char, count: usize) -> Option<Vec<PathBuf>> {
    if paths.is_null() && count > 0 {
        return None;
    }
    let mut list = Vec::with_capacity(count);
    for index in 0..count {
        list.push(PathBuf::from(unsafe { borrow(*paths.add(index)) }?));
    }
    Some(list)
}

/// Borrows the optional `text` argument: null means "as compiled", and a
/// string that is not UTF-8 is refused rather than ignored.
unsafe fn optional_text<'a>(text: *const c_char) -> Result<Option<&'a str>, ()> {
    if text.is_null() {
        return Ok(None);
    }
    unsafe { borrow(text) }.map(Some).ok_or(())
}

/// Where the name at `offset` was declared, in `text` when the editor holds
/// changes it has not saved (null means the file as compiled or opened).
///
/// The compiler answers once the project is compiled; the index before that,
/// and whenever the compiler does not know. Free with `rln_locations_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_definition_in(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnLocations,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.definition_in(path, offset, text) {
            Ok(definition) => {
                unsafe {
                    write_locations(
                        out,
                        &definition.word,
                        &definition.targets,
                        definition.certain,
                    )
                };
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

/// Every use of the name at `offset` across the project, its declarations
/// included. Free with `rln_locations_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_references(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnLocations,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.references(path, offset, text) {
            Ok(uses) => {
                unsafe { write_locations(out, &uses.word, &uses.locations, true) };
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

unsafe fn write_locations(
    out: *mut RlnLocations,
    word: &str,
    locations: &[Location],
    certain: bool,
) {
    let mut strings = Strings::default();
    let word = strings.add(word);
    let items = pack_locations(locations, &mut strings);
    let (items, count) = leak(items);
    let (bytes, strings_length) = leak(strings.bytes);
    unsafe {
        out.write(RlnLocations {
            items,
            count,
            strings: bytes,
            strings_length,
            word,
            certain,
        });
    }
}

/// What can be written at `offset`. Free with `rln_completions_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_completions(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnCompletions,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.completions(path, offset, text) {
            Ok(list) => {
                let mut strings = Strings::default();
                // A caller of this older call writes the label: a snippet
                // written as its shortcut is no use to it.
                let items: Vec<RlnCompletion> = list
                    .items
                    .iter()
                    .filter(|item| !item.is_snippet)
                    .map(|item| RlnCompletion {
                        label: strings.add(&item.label),
                        detail: strings.add(&item.detail),
                        kind: item.kind as u8,
                        rank: item.rank,
                    })
                    .collect();
                let (items, count) = leak(items);
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnCompletions {
                        items,
                        count,
                        strings: bytes,
                        strings_length,
                        start: list.start,
                    });
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_completions_free(completions: RlnCompletions) {
    shallow((), || unsafe {
        reclaim(completions.items, completions.count);
        reclaim(completions.strings, completions.strings_length);
    });
}

/// The name at `offset` as one line — `int Count`, `void Add(T item)` — for
/// a tooltip. Free the text with `rln_text_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_describe(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnString,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.describe(path, offset, text) {
            Ok(line) => {
                let (bytes, length) = leak(line.into_bytes());
                unsafe { out.write(RlnString { bytes, length }) };
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

/// What is wrong with the file as the editor has it: syntax errors, and —
/// once the project is compiled — what declaring and binding it finds. Free
/// with `rln_diagnostics_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_diagnostics(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    out: *mut RlnDiagnostics,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.diagnostics(path, text) {
            Ok(found) => {
                let mut strings = Strings::default();
                let items: Vec<RlnDiagnostic> = found
                    .items
                    .iter()
                    .map(|item| RlnDiagnostic {
                        start: item.start,
                        length: item.length,
                        severity: item.severity,
                        tags: u8::from(item.unnecessary) | (u8::from(item.deprecated) << 1),
                        code: strings.add(&item.code),
                        message: strings.add(&item.message),
                    })
                    .collect();
                let (items, count) = leak(items);
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnDiagnostics {
                        items,
                        count,
                        strings: bytes,
                        strings_length,
                        semantic: found.semantic,
                    });
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_diagnostics_free(diagnostics: RlnDiagnostics) {
    shallow((), || unsafe {
        reclaim(diagnostics.items, diagnostics.count);
        reclaim(diagnostics.strings, diagnostics.strings_length);
    });
}

/// The overloads of the call whose argument list holds `offset`, which fits
/// best, and which parameter the cursor is at. Free with
/// `rln_signatures_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_signatures(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnSignatures,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.signatures(path, offset, text) {
            Ok(found) => {
                let mut strings = Strings::default();
                let mut parameters: Vec<RlnRange> = Vec::new();
                let items: Vec<RlnSignature> = found
                    .items
                    .iter()
                    .map(|item| {
                        let first_parameter = parameters.len() as u32;
                        parameters.extend(
                            item.parameters
                                .iter()
                                .map(|&(start, end)| RlnRange { start, end }),
                        );
                        RlnSignature {
                            label: strings.add(&item.label),
                            first_parameter,
                            parameter_count: item.parameters.len() as u32,
                        }
                    })
                    .collect();
                let (items, count) = leak(items);
                let (parameters, parameter_count) = leak(parameters);
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnSignatures {
                        items,
                        count,
                        parameters,
                        parameter_count,
                        strings: bytes,
                        strings_length,
                        active: found.active as u32,
                        parameter: found.parameter as u32,
                    });
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_signatures_free(signatures: RlnSignatures) {
    shallow((), || unsafe {
        reclaim(signatures.items, signatures.count);
        reclaim(signatures.parameters, signatures.parameter_count);
        reclaim(signatures.strings, signatures.strings_length);
    });
}

/// The documentation of the name at `offset`: its `///` comment, or the XML
/// file beside the assembly it comes from. Free with
/// `rln_documentation_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_documentation(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnDocumentation,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.documentation(path, offset, text) {
            Ok(found) => {
                let mut strings = Strings::default();
                let signature = strings.add(&found.signature);
                let container = strings.add(&found.container);
                let summary = strings.add(&found.summary);
                let returns = strings.add(&found.returns);
                let parameters: Vec<RlnDocParameter> = found
                    .parameters
                    .iter()
                    .map(|(name, text)| RlnDocParameter {
                        name: strings.add(name),
                        text: strings.add(text),
                    })
                    .collect();
                let (parameters, parameter_count) = leak(parameters);
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnDocumentation {
                        signature,
                        container,
                        summary,
                        returns,
                        parameters,
                        parameter_count,
                        strings: bytes,
                        strings_length,
                    });
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_documentation_free(documentation: RlnDocumentation) {
    shallow((), || unsafe {
        reclaim(documentation.parameters, documentation.parameter_count);
        reclaim(documentation.strings, documentation.strings_length);
    });
}

/// Ever larger pieces of code around `start..end` (UTF-16), smallest first:
/// what extend selection steps through. Syntax only, so it answers before
/// the project is compiled. Free with `rln_ranges_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_selection_ranges(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    start: u32,
    end: u32,
    out: *mut RlnRanges,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.selection_ranges(path, start, end, text) {
            Ok(found) => {
                let items: Vec<RlnRange> = found
                    .into_iter()
                    .map(|(start, end)| RlnRange { start, end })
                    .collect();
                let (items, count) = leak(items);
                unsafe { out.write(RlnRanges { items, count }) };
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_ranges_free(ranges: RlnRanges) {
    shallow((), || unsafe { reclaim(ranges.items, ranges.count) });
}

/// The number of completion kinds, for checking a caller's table.
#[unsafe(no_mangle)]
pub extern "C" fn rln_completion_kind_count() -> u32 {
    CompletionKind::Snippet as u32 + 1
}

// MARK: - edits

/// Packs changes into the shared arrays, returning where they went.
fn pack_changes(
    changes: &rustlyn_ide::session::Changes,
    strings: &mut Strings,
    edits: &mut Vec<RlnEdit>,
    renames: &mut Vec<RlnRename>,
) -> (u32, u32, u32, u32) {
    let first_edit = edits.len() as u32;
    let first_rename = renames.len() as u32;
    for change in &changes.changes {
        edits.push(RlnEdit {
            path: strings.add(&change.path.to_string_lossy()),
            text: strings.add(&change.text),
            start: change.start,
            length: change.length,
        });
    }
    for (from, to) in &changes.renames {
        renames.push(RlnRename {
            from: strings.add(&from.to_string_lossy()),
            to: strings.add(&to.to_string_lossy()),
        });
    }
    (
        first_edit,
        changes.changes.len() as u32,
        first_rename,
        changes.renames.len() as u32,
    )
}

/// Hands `changes` to C as an `RlnEdits`.
unsafe fn write_edits(out: *mut RlnEdits, changes: &rustlyn_ide::session::Changes) {
    let mut strings = Strings::default();
    let mut edits = Vec::new();
    let mut renames = Vec::new();
    pack_changes(changes, &mut strings, &mut edits, &mut renames);
    let (items, count) = leak(edits);
    let (renames, rename_count) = leak(renames);
    let (bytes, strings_length) = leak(strings.bytes);
    unsafe {
        out.write(RlnEdits {
            items,
            count,
            renames,
            rename_count,
            strings: bytes,
            strings_length,
        });
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_edits_free(edits: RlnEdits) {
    shallow((), || unsafe {
        reclaim(edits.items, edits.count);
        reclaim(edits.renames, edits.rename_count);
        reclaim(edits.strings, edits.strings_length);
    });
}

/// Whether `path` is source a generator wrote (in a Unity project, what its
/// source generators left for the compiler): compiled and navigable, never
/// edited. False for a null or non-UTF-8 argument.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_is_generated(session: *mut RlnSession, path: *const c_char) -> bool {
    guard(false, || {
        let (Some(session), Some(path)) = (unsafe { held(session) }, unsafe { borrow(path) })
        else {
            return false;
        };
        session.session.is_generated(path)
    })
}

/// What the light bulb offers for `start..end` (UTF-16; equal for a
/// cursor): fixes for the diagnostics there, and refactorings of the
/// selection. Each comes with its edits. Free with `rln_code_actions_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_code_actions(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    start: u32,
    end: u32,
    out: *mut RlnCodeActions,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.code_actions(path, start, end, text) {
            Ok(actions) => {
                let mut strings = Strings::default();
                let mut edits = Vec::new();
                let mut renames = Vec::new();
                let items: Vec<RlnCodeAction> = actions
                    .iter()
                    .map(|action| {
                        let title = strings.add(&action.title);
                        let fixes = strings.add(action.fixes.as_deref().unwrap_or(""));
                        let (first_edit, edit_count, first_rename, rename_count) =
                            pack_changes(&action.changes, &mut strings, &mut edits, &mut renames);
                        RlnCodeAction {
                            title,
                            fixes,
                            first_edit,
                            edit_count,
                            first_rename,
                            rename_count,
                            kind: action.kind as u8,
                        }
                    })
                    .collect();
                let (items, count) = leak(items);
                let (edits, edit_count) = leak(edits);
                let (renames, rename_count) = leak(renames);
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnCodeActions {
                        items,
                        count,
                        edits,
                        edit_count,
                        renames,
                        rename_count,
                        strings: bytes,
                        strings_length,
                    });
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_code_actions_free(actions: RlnCodeActions) {
    shallow((), || unsafe {
        reclaim(actions.items, actions.count);
        reclaim(actions.edits, actions.edit_count);
        reclaim(actions.renames, actions.rename_count);
        reclaim(actions.strings, actions.strings_length);
    });
}

/// The number of action kinds, for checking a caller's table.
#[unsafe(no_mangle)]
pub extern "C" fn rln_action_kind_count() -> u32 {
    rustlyn_ide::semantic::ActionKind::Generate as u32 + 1
}

// MARK: - semantic colouring, highlights, detailed references, code lens

/// A name coloured by what it refers to, in UTF-16 code units.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnSemanticRun {
    pub start: u32,
    pub length: u32,
    /// `SemanticModifiers` bits: static, reassigned, deprecated, abstract,
    /// readonly, async, declaration, from a referenced library.
    pub modifiers: u32,
    /// A `SemanticClass`, as its discriminant.
    pub class: u8,
}

/// Semantic runs. Freed with `rln_semantic_runs_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnSemanticRuns {
    pub items: *const RlnSemanticRun,
    pub count: usize,
}

/// A span to highlight, in UTF-16 code units.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnHighlight {
    pub start: u32,
    pub length: u32,
    /// A `HighlightKind`: 0 a keyword, 1 definition, 2 read, 3 write.
    pub kind: u8,
}

/// Highlights. Freed with `rln_highlights_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnHighlights {
    pub items: *const RlnHighlight,
    pub count: usize,
}

/// One entry of a references list.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnReference {
    /// Relative to the project root.
    pub path: RlnText,
    /// The member or type it is in.
    pub container: RlnText,
    /// Its line, trimmed.
    pub preview: RlnText,
    pub line: u32,
    /// UTF-16 code units from the start of the line.
    pub character: u32,
    pub length: u32,
    /// A `ReferenceKind`: 0 definition, 1 write, 2 read.
    pub kind: u8,
}

/// A references list. Freed with `rln_references_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnReferences {
    pub items: *const RlnReference,
    pub count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
    pub word: RlnText,
}

/// A reference count over a declaration's name, in UTF-16 code units.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnLens {
    pub start: u32,
    pub length: u32,
    pub count: u32,
}

/// Code lenses. Freed with `rln_lenses_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnLenses {
    pub items: *const RlnLens,
    pub count: usize,
}

/// The names in `start..end` (UTF-16) coloured by what they refer to. Free
/// with `rln_semantic_runs_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_semantic_tokens(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    start: u32,
    end: u32,
    out: *mut RlnSemanticRuns,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.semantic_tokens(path, start, end, text) {
            Ok(found) => {
                let items: Vec<RlnSemanticRun> = found
                    .iter()
                    .map(|run| RlnSemanticRun {
                        start: run.start,
                        length: run.length,
                        modifiers: run.modifiers.bits(),
                        class: run.class as u8,
                    })
                    .collect();
                let (items, count) = leak(items);
                unsafe { out.write(RlnSemanticRuns { items, count }) };
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_semantic_runs_free(runs: RlnSemanticRuns) {
    shallow((), || unsafe { reclaim(runs.items, runs.count) });
}

/// What to highlight for the cursor at `offset`: the occurrences of the
/// symbol under it, or the keywords of the construct under it. Free with
/// `rln_highlights_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_highlights(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnHighlights,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.document_highlights(path, offset, text) {
            Ok(found) => {
                let items: Vec<RlnHighlight> = found
                    .iter()
                    .map(|run| RlnHighlight {
                        start: run.start,
                        length: run.length,
                        kind: run.kind as u8,
                    })
                    .collect();
                let (items, count) = leak(items);
                unsafe { out.write(RlnHighlights { items, count }) };
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_highlights_free(highlights: RlnHighlights) {
    shallow((), || unsafe {
        reclaim(highlights.items, highlights.count)
    });
}

/// Every reference to the name at `offset`, classified, with its member
/// and line. Free with `rln_references_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_references_detailed(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnReferences,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.references_detailed(path, offset, text) {
            Ok(uses) => {
                let mut strings = Strings::default();
                let word = strings.add(&uses.word);
                let items: Vec<RlnReference> = uses
                    .items
                    .iter()
                    .map(|item| RlnReference {
                        path: strings.add(&item.path.to_string_lossy()),
                        container: strings.add(&item.container),
                        preview: strings.add(&item.preview),
                        line: item.line,
                        character: item.character,
                        length: item.length,
                        kind: item.kind as u8,
                    })
                    .collect();
                let (items, count) = leak(items);
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnReferences {
                        items,
                        count,
                        strings: bytes,
                        strings_length,
                        word,
                    });
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_references_free(references: RlnReferences) {
    shallow((), || unsafe {
        reclaim(references.items, references.count);
        reclaim(references.strings, references.strings_length);
    });
}

/// A reference count for every type and member the file declares. Free
/// with `rln_lenses_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_code_lens(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    out: *mut RlnLenses,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.code_lens(path, text) {
            Ok(found) => {
                let items: Vec<RlnLens> = found
                    .iter()
                    .map(|lens| RlnLens {
                        start: lens.start,
                        length: lens.length,
                        count: lens.count,
                    })
                    .collect();
                let (items, count) = leak(items);
                unsafe { out.write(RlnLenses { items, count }) };
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

/// Calls off every `rln_code_lens` running on the session: each stops at the
/// next file it would search and returns `RLN_CANCELLED`. One begun after
/// this call is not affected. Any thread.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_cancel_code_lens(session: *mut RlnSession) {
    shallow((), || {
        if let Some(session) = unsafe { held(session) } {
            session.session.cancel_code_lens();
        }
    });
}

/// Where `rln_code_lens` puts its counts, in the same order, without
/// counting: `count` is `UINT32_MAX`. Only this file is looked at, so it is
/// cheap enough to ask while the file opens. Free with `rln_lenses_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_code_lens_places(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    out: *mut RlnLenses,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.code_lens_places(path, text) {
            Ok(found) => {
                let items: Vec<RlnLens> = found
                    .iter()
                    .map(|lens| RlnLens {
                        start: lens.start,
                        length: lens.length,
                        count: lens.count,
                    })
                    .collect();
                let (items, count) = leak(items);
                unsafe { out.write(RlnLenses { items, count }) };
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_lenses_free(lenses: RlnLenses) {
    shallow((), || unsafe { reclaim(lenses.items, lenses.count) });
}

/// The number of semantic classes, for checking a caller's table.
#[unsafe(no_mangle)]
pub extern "C" fn rln_semantic_class_count() -> u32 {
    rustlyn_ide::semantic::SemanticClass::count()
}

const _: () = {
    assert!(size_of::<RlnSemanticRun>() == 16);
    assert!(size_of::<RlnHighlight>() == 12);
    assert!(size_of::<RlnReference>() == 40);
    assert!(size_of::<RlnLens>() == 12);
};

// MARK: - rename

/// Whether the name at the cursor can be renamed, and where it is. Freed
/// with `rln_rename_info_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnRenameInfo {
    /// UTF-16 offset and length of the name.
    pub start: u32,
    pub length: u32,
    /// The name as written, to fill the rename box with.
    pub text: RlnText,
    /// What is being renamed, as one line.
    pub description: RlnText,
    /// Why it cannot be renamed; empty when it can.
    pub refused: RlnText,
    pub can_rename: u8,
    pub strings: *const u8,
    pub strings_length: usize,
}

/// A place a rename would break.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnConflict {
    pub path: RlnText,
    pub message: RlnText,
    /// UTF-16, in the text the edits to that file count in.
    pub start: u32,
    pub length: u32,
    /// Whether the edits already put it right, by qualifying the name.
    pub resolved: u8,
}

/// A rename: its edits, the files to rename, and its conflicts. The texts
/// of the conflicts and of `refused` are in `edits.strings`. Freed with
/// `rln_rename_result_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnRenameResult {
    pub edits: RlnEdits,
    pub conflicts: *const RlnConflict,
    pub conflict_count: usize,
    /// Why nothing was renamed; empty when it was.
    pub refused: RlnText,
}

/// Whether what is at `offset` (UTF-16) can be renamed. A name that cannot
/// be is `RLN_OK` with `can_rename` clear and the reason in `refused`.
/// Free with `rln_rename_info_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_prepare_rename(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnRenameInfo,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.prepare_rename(path, offset, text) {
            Ok(info) => {
                let mut strings = Strings::default();
                let name = strings.add(&info.text);
                let description = strings.add(&info.description);
                let refused = strings.add(info.refused.as_deref().unwrap_or(""));
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnRenameInfo {
                        start: info.start,
                        length: info.length,
                        text: name,
                        description,
                        refused,
                        can_rename: u8::from(info.refused.is_none()),
                        strings: bytes,
                        strings_length,
                    });
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_rename_info_free(info: RlnRenameInfo) {
    shallow((), || unsafe {
        reclaim(info.strings, info.strings_length);
    });
}

/// Renames what is at `offset` (UTF-16) of `path` to `new_name`, with the
/// `RLN_RENAME_*` flags. A rename that cannot be done is `RLN_OK` with the
/// reason in `refused` and no edits. Free with `rln_rename_result_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_rename(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    new_name: *const c_char,
    flags: u32,
    out: *mut RlnRenameResult,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text), Some(new_name)) = (
            unsafe { held(session) },
            unsafe { borrow(path) },
            unsafe { optional_text(text) },
            unsafe { borrow(new_name) },
        ) else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        let options = rustlyn_ide::semantic::RenameOptions::from_flags(flags);
        match session
            .session
            .rename(path, offset, new_name, text, options)
        {
            Ok(result) => {
                let mut strings = Strings::default();
                let mut edits = Vec::new();
                let mut renames = Vec::new();
                pack_changes(&result.changes, &mut strings, &mut edits, &mut renames);
                let conflicts: Vec<RlnConflict> = result
                    .conflicts
                    .iter()
                    .map(|conflict| RlnConflict {
                        path: strings.add(&conflict.path.to_string_lossy()),
                        message: strings.add(&conflict.message),
                        start: conflict.start,
                        length: conflict.length,
                        resolved: u8::from(conflict.resolved),
                    })
                    .collect();
                let refused = strings.add(result.refused.as_deref().unwrap_or(""));
                let (items, count) = leak(edits);
                let (renames, rename_count) = leak(renames);
                let (conflicts, conflict_count) = leak(conflicts);
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnRenameResult {
                        edits: RlnEdits {
                            items,
                            count,
                            renames,
                            rename_count,
                            strings: bytes,
                            strings_length,
                        },
                        conflicts,
                        conflict_count,
                        refused,
                    });
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_rename_result_free(result: RlnRenameResult) {
    shallow((), || unsafe {
        reclaim(result.conflicts, result.conflict_count);
        rln_edits_free(result.edits);
    });
}

/// The layout the header promises for rename, and the flags it spells out.
const _: () = {
    use rustlyn_ide::semantic::RenameOptions;
    assert!(size_of::<RlnConflict>() == 28);
    assert!(RenameOptions::IN_COMMENTS == 1);
    assert!(RenameOptions::IN_STRINGS == 2);
    assert!(RenameOptions::OVERLOADS == 4);
    assert!(RenameOptions::FILE == 8);
};

// MARK: - navigation: type definition, bases, implementations, hierarchies, search

use rustlyn_ide::search::SearchKind;
use rustlyn_ide::session::{Call, Item};

/// A node of a call or type hierarchy.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnHierarchyItem {
    pub name: RlnText,
    /// The signature: `double Area()`, `class Circle`.
    pub detail: RlnText,
    /// The qualified name of the type or namespace it is in.
    pub container: RlnText,
    /// What to pass to `rln_incoming_calls` and the rest to expand it.
    pub key: RlnText,
    /// Relative to the project root; an assembly's path for a declaration
    /// in one. Empty when `has_location` is false.
    pub path: RlnText,
    /// The name, which a jump selects.
    pub line: u32,
    pub character: u32,
    pub length: u32,
    /// The whole declaration.
    pub start_line: u32,
    pub start_character: u32,
    pub end_line: u32,
    pub end_character: u32,
    pub kind: u8,
    pub has_location: bool,
}

/// Hierarchy items. Freed with `rln_hierarchy_items_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnHierarchyItems {
    pub items: *const RlnHierarchyItem,
    pub count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
}

/// From one line and column to another, the columns in UTF-16 code units.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnLineRange {
    pub start_line: u32,
    pub start_character: u32,
    pub end_line: u32,
    pub end_character: u32,
}

/// A caller or a callee, with where the calls are: `range_count` of the
/// call list's `ranges` from `first_range`, in the file `path`.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnCall {
    pub item: RlnHierarchyItem,
    pub path: RlnText,
    pub first_range: u32,
    pub range_count: u32,
    /// The calls name a member the one asked about overrides or implements.
    pub through_base: bool,
}

/// Calls. Freed with `rln_calls_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnCalls {
    pub items: *const RlnCall,
    pub count: usize,
    pub ranges: *const RlnLineRange,
    pub range_count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
}

/// One Navigate To result: `range_count` of the list's `ranges` from
/// `first_range` are the UTF-16 ranges of `name` that matched.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnSearchResult {
    /// Where to go. `location.name` is the qualified name.
    pub location: RlnLocation,
    /// The name as matched.
    pub name: RlnText,
    pub container: RlnText,
    pub first_range: u32,
    pub range_count: u32,
    /// `MatchKind`: 0 exact, 1 prefix, ... 9 fuzzy. Lower is better.
    pub match_kind: u8,
    pub case_sensitive: bool,
    pub is_file: bool,
}

/// Navigate To results. Freed with `rln_search_results_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnSearchResults {
    pub items: *const RlnSearchResult,
    pub count: usize,
    pub ranges: *const RlnRange,
    pub range_count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
}

/// The shape of the calls that answer with places at a cursor.
type PlacesQuestion =
    fn(&Session, &str, u32, Option<&str>) -> Result<rustlyn_ide::Definition, Refusal>;

/// Asks one of the questions whose answer is places, and writes them out.
unsafe fn places_at(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnLocations,
    question: PlacesQuestion,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match question(&session.session, path, offset, text) {
            Ok(definition) => {
                unsafe {
                    write_locations(
                        out,
                        &definition.word,
                        &definition.targets,
                        definition.certain,
                    );
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

/// Where the type of the name at `offset` is declared. Free with
/// `rln_locations_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_type_definition(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnLocations,
) -> RlnStatus {
    unsafe {
        places_at(
            session,
            path,
            text,
            offset,
            out,
            |session, path, offset, text| session.type_definition(path, offset, text),
        )
    }
}

/// What the type or member at `offset` derives from, overrides or
/// implements, nearest first. Free with `rln_locations_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_bases(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnLocations,
) -> RlnStatus {
    unsafe {
        places_at(
            session,
            path,
            text,
            offset,
            out,
            |session, path, offset, text| session.bases(path, offset, text),
        )
    }
}

/// What implements the type or member at `offset`: from the compiler once
/// the project is compiled, from the index before. Free with
/// `rln_locations_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_implementations_in(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnLocations,
) -> RlnStatus {
    unsafe {
        places_at(
            session,
            path,
            text,
            offset,
            out,
            |session, path, offset, text| session.implementations_in(path, offset, text),
        )
    }
}

/// The types derived from the type at `offset`, however indirectly: classes
/// and structs, or with `interfaces` the interfaces that extend it. Free
/// with `rln_locations_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_derived_types(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    interfaces: bool,
    out: *mut RlnLocations,
) -> RlnStatus {
    let question: PlacesQuestion = if interfaces {
        |session, path, offset, text| session.derived_types(path, offset, text, true)
    } else {
        |session, path, offset, text| session.derived_types(path, offset, text, false)
    };
    unsafe { places_at(session, path, text, offset, out, question) }
}

fn pack_item(item: &Item, strings: &mut Strings) -> RlnHierarchyItem {
    let location = item.location.as_ref();
    let range = item.range.unwrap_or_default();
    RlnHierarchyItem {
        name: strings.add(&item.name),
        detail: strings.add(&item.detail),
        container: strings.add(&item.container),
        key: strings.add(&item.key),
        path: strings.add(&location.map_or_else(String::new, |location| {
            location.path.to_string_lossy().into_owned()
        })),
        line: location.map_or(0, |location| location.line),
        character: location.map_or(0, |location| location.character),
        length: location.map_or(0, |location| location.length),
        start_line: range.start_line,
        start_character: range.start_character,
        end_line: range.end_line,
        end_character: range.end_character,
        kind: item.kind as u8,
        has_location: location.is_some(),
    }
}

unsafe fn write_items(out: *mut RlnHierarchyItems, items: &[Item]) {
    let mut strings = Strings::default();
    let items: Vec<RlnHierarchyItem> = items
        .iter()
        .map(|item| pack_item(item, &mut strings))
        .collect();
    let (items, count) = leak(items);
    let (bytes, strings_length) = leak(strings.bytes);
    unsafe {
        out.write(RlnHierarchyItems {
            items,
            count,
            strings: bytes,
            strings_length,
        });
    }
}

unsafe fn write_calls(out: *mut RlnCalls, calls: &[Call]) {
    let mut strings = Strings::default();
    let mut ranges: Vec<RlnLineRange> = Vec::new();
    let items: Vec<RlnCall> = calls
        .iter()
        .map(|call| {
            let first_range = ranges.len() as u32;
            ranges.extend(call.ranges.iter().map(|range| RlnLineRange {
                start_line: range.start_line,
                start_character: range.start_character,
                end_line: range.end_line,
                end_character: range.end_character,
            }));
            RlnCall {
                item: pack_item(&call.item, &mut strings),
                path: strings.add(&call.path.to_string_lossy()),
                first_range,
                range_count: call.ranges.len() as u32,
                through_base: call.through_base,
            }
        })
        .collect();
    let (items, count) = leak(items);
    let (ranges, range_count) = leak(ranges);
    let (bytes, strings_length) = leak(strings.bytes);
    unsafe {
        out.write(RlnCalls {
            items,
            count,
            ranges,
            range_count,
            strings: bytes,
            strings_length,
        });
    }
}

/// The root of a hierarchy at a cursor: one item.
unsafe fn hierarchy_root(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnHierarchyItems,
    question: fn(&Session, &str, u32, Option<&str>) -> Result<Item, Refusal>,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match question(&session.session, path, offset, text) {
            Ok(item) => {
                unsafe { write_items(out, std::slice::from_ref(&item)) };
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

/// Items related to the item `key` names.
unsafe fn related_items(
    session: *mut RlnSession,
    key: *const c_char,
    out: *mut RlnHierarchyItems,
    question: fn(&Session, &str) -> Result<Vec<Item>, Refusal>,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(key)) = (unsafe { held(session) }, unsafe { borrow(key) }) else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match question(&session.session, key) {
            Ok(items) => {
                unsafe { write_items(out, &items) };
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

/// Calls to or from the member `key` names.
unsafe fn calls_of(
    session: *mut RlnSession,
    key: *const c_char,
    out: *mut RlnCalls,
    question: fn(&Session, &str) -> Result<Vec<Call>, Refusal>,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(key)) = (unsafe { held(session) }, unsafe { borrow(key) }) else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match question(&session.session, key) {
            Ok(calls) => {
                unsafe { write_calls(out, &calls) };
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

/// The method, constructor, property, event or field at `offset`, as the
/// root of a call hierarchy: one item. Free with `rln_hierarchy_items_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_call_hierarchy(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnHierarchyItems,
) -> RlnStatus {
    unsafe {
        hierarchy_root(
            session,
            path,
            text,
            offset,
            out,
            |session, path, offset, text| session.call_hierarchy(path, offset, text),
        )
    }
}

/// Who calls the member `key` names. Free with `rln_calls_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_incoming_calls(
    session: *mut RlnSession,
    key: *const c_char,
    out: *mut RlnCalls,
) -> RlnStatus {
    unsafe { calls_of(session, key, out, Session::incoming_calls) }
}

/// What the member `key` names calls. Free with `rln_calls_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_outgoing_calls(
    session: *mut RlnSession,
    key: *const c_char,
    out: *mut RlnCalls,
) -> RlnStatus {
    unsafe { calls_of(session, key, out, Session::outgoing_calls) }
}

/// The type at `offset`, or the type of what is there, as the root of a
/// type hierarchy: one item. Free with `rln_hierarchy_items_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_type_hierarchy(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnHierarchyItems,
) -> RlnStatus {
    unsafe {
        hierarchy_root(
            session,
            path,
            text,
            offset,
            out,
            |session, path, offset, text| session.type_hierarchy(path, offset, text),
        )
    }
}

/// The base class and interfaces of the type `key` names. Free with
/// `rln_hierarchy_items_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_supertypes(
    session: *mut RlnSession,
    key: *const c_char,
    out: *mut RlnHierarchyItems,
) -> RlnStatus {
    unsafe { related_items(session, key, out, Session::supertypes) }
}

/// The project's types that derive from the type `key` names. Free with
/// `rln_hierarchy_items_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_subtypes(
    session: *mut RlnSession,
    key: *const c_char,
    out: *mut RlnHierarchyItems,
) -> RlnStatus {
    unsafe { related_items(session, key, out, Session::subtypes) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_hierarchy_items_free(items: RlnHierarchyItems) {
    shallow((), || unsafe {
        reclaim(items.items, items.count);
        reclaim(items.strings, items.strings_length);
    });
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_calls_free(calls: RlnCalls) {
    shallow((), || unsafe {
        reclaim(calls.items, calls.count);
        reclaim(calls.ranges, calls.range_count);
        reclaim(calls.strings, calls.strings_length);
    });
}

/// Declarations and files whose names `pattern` matches, best first, at most
/// `limit`: Navigate To. `kind` is 0 for everything, 1 types, 2 members,
/// 3 files. Answers from the index. Free with `rln_search_results_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_search(
    session: *mut RlnSession,
    pattern: *const c_char,
    kind: u8,
    limit: u32,
    out: *mut RlnSearchResults,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(pattern)) = (unsafe { held(session) }, unsafe { borrow(pattern) })
        else {
            return RlnStatus::BadArgument;
        };
        let kind = match kind {
            0 => SearchKind::All,
            1 => SearchKind::Types,
            2 => SearchKind::Members,
            3 => SearchKind::Files,
            _ => return RlnStatus::BadArgument,
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.search(pattern, kind, limit as usize) {
            Ok(results) => {
                let mut strings = Strings::default();
                let mut ranges: Vec<RlnRange> = Vec::new();
                let items: Vec<RlnSearchResult> = results
                    .iter()
                    .map(|result| {
                        let first_range = ranges.len() as u32;
                        ranges.extend(
                            result
                                .ranges
                                .iter()
                                .map(|&(start, end)| RlnRange { start, end }),
                        );
                        let location =
                            &pack_locations(std::slice::from_ref(&result.location), &mut strings)
                                [0];
                        RlnSearchResult {
                            location: *location,
                            name: strings.add(&result.name),
                            container: strings.add(&result.container),
                            first_range,
                            range_count: result.ranges.len() as u32,
                            match_kind: result.match_kind as u8,
                            case_sensitive: result.case_sensitive,
                            is_file: result.is_file,
                        }
                    })
                    .collect();
                let (items, count) = leak(items);
                let (ranges, range_count) = leak(ranges);
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnSearchResults {
                        items,
                        count,
                        ranges,
                        range_count,
                        strings: bytes,
                        strings_length,
                    });
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_search_results_free(results: RlnSearchResults) {
    shallow((), || unsafe {
        reclaim(results.items, results.count);
        reclaim(results.ranges, results.range_count);
        reclaim(results.strings, results.strings_length);
    });
}

/// The sizes `include/rustlyn.h` states for the structs above.
const _: () = {
    assert!(size_of::<RlnHierarchyItem>() == 72);
    assert!(size_of::<RlnLineRange>() == 16);
    assert!(size_of::<RlnCall>() == 92);
    assert!(size_of::<RlnSearchResult>() == 60);
};

// MARK: - completion parity

/// One completion with everything needed to commit it. An empty text means
/// "the label" for `insert_text` and `filter_text`, and "the editor's usual
/// ones" for `commit_characters`.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnCompletionItem {
    pub label: RlnText,
    pub detail: RlnText,
    pub insert_text: RlnText,
    pub filter_text: RlnText,
    pub commit_characters: RlnText,
    /// This item's edits elsewhere in the file — the `using` an unimported
    /// type needs — as a run of `RlnCompletionItems.edits`.
    pub edits_start: u32,
    pub edits_count: u32,
    /// Where the cursor goes, in UTF-16 code units into the inserted text;
    /// `u32::MAX` for its end.
    pub caret: u32,
    /// A `CompletionKind`, as its discriminant.
    pub kind: u8,
    /// Lower sorts first.
    pub rank: u8,
    pub preselect: u8,
    pub is_snippet: u8,
}

/// One replacement in the file asked about: `length` UTF-16 code units at
/// `start` become `text`.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnTextEdit {
    pub start: u32,
    pub length: u32,
    pub text: RlnText,
}

/// A completion list with everything in it. Freed with
/// `rln_completion_items_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnCompletionItems {
    pub items: *const RlnCompletionItem,
    pub count: usize,
    pub edits: *const RlnTextEdit,
    pub edit_count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
    /// Where the word being completed starts, in UTF-16 code units.
    pub start: u32,
    /// Where a new name is being written: commit nothing on a space.
    pub suggestion_mode: u8,
}

/// What can be written at `offset`, with insert texts, preselection and the
/// edits that go with each item. Free with `rln_completion_items_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_completions_ex(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnCompletionItems,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.completions(path, offset, text) {
            Ok(list) => {
                let mut strings = Strings::default();
                let mut edits = Vec::new();
                let mut items = Vec::with_capacity(list.items.len());
                for item in &list.items {
                    let edits_start = edits.len() as u32;
                    for edit in &item.additional_edits {
                        edits.push(RlnTextEdit {
                            start: edit.span.start(),
                            length: edit.span.length(),
                            text: strings.add(&edit.text),
                        });
                    }
                    items.push(RlnCompletionItem {
                        label: strings.add(&item.label),
                        detail: strings.add(&item.detail),
                        insert_text: strings.add(item.insert_text.as_deref().unwrap_or("")),
                        filter_text: strings.add(item.filter_text.as_deref().unwrap_or("")),
                        commit_characters: strings.add(&item.commit_characters),
                        edits_start,
                        edits_count: item.additional_edits.len() as u32,
                        caret: item.caret.unwrap_or(u32::MAX),
                        kind: item.kind as u8,
                        rank: item.rank,
                        preselect: u8::from(item.preselect),
                        is_snippet: u8::from(item.is_snippet),
                    });
                }
                let (items, count) = leak(items);
                let (edits, edit_count) = leak(edits);
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnCompletionItems {
                        items,
                        count,
                        edits,
                        edit_count,
                        strings: bytes,
                        strings_length,
                        start: list.start,
                        suggestion_mode: u8::from(list.suggestion_mode),
                    });
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_completion_items_free(list: RlnCompletionItems) {
    shallow((), || unsafe {
        reclaim(list.items, list.count);
        reclaim(list.edits, list.edit_count);
        reclaim(list.strings, list.strings_length);
    });
}

/// The documentation of the completion item labelled `label` at `offset`:
/// what to show beside the selected item. Free with
/// `rln_documentation_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_completion_description(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    label: *const c_char,
    out: *mut RlnDocumentation,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text), Some(label)) = (
            unsafe { held(session) },
            unsafe { borrow(path) },
            unsafe { optional_text(text) },
            unsafe { borrow(label) },
        ) else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session
            .session
            .completion_description(path, offset, text, label)
        {
            Ok(found) => {
                let mut strings = Strings::default();
                let signature = strings.add(&found.signature);
                let container = strings.add(&found.container);
                let summary = strings.add(&found.summary);
                let returns = strings.add(&found.returns);
                let parameters: Vec<RlnDocParameter> = found
                    .parameters
                    .iter()
                    .map(|(name, text)| RlnDocParameter {
                        name: strings.add(name),
                        text: strings.add(text),
                    })
                    .collect();
                let (parameters, parameter_count) = leak(parameters);
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnDocumentation {
                        signature,
                        container,
                        summary,
                        returns,
                        parameters,
                        parameter_count,
                        strings: bytes,
                        strings_length,
                    });
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

/// Whether typing the character `typed` (a Unicode scalar value) into
/// `text`, leaving the cursor at `offset` (UTF-16, after it), should open
/// the completion list. Syntax only.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_completion_trigger(
    session: *mut RlnSession,
    text: *const c_char,
    offset: u32,
    typed: u32,
    out: *mut bool,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(text), Some(typed)) = (
            unsafe { held(session) },
            unsafe { borrow(text) },
            char::from_u32(typed),
        ) else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        let opens = session.session.completion_trigger(text, offset, typed);
        unsafe { out.write(opens) };
        RlnStatus::Ok
    })
}

/// The layout the header promises for completion items.
const _: () = {
    assert!(size_of::<RlnCompletionItem>() == 56);
    assert!(size_of::<RlnTextEdit>() == 16);
    assert!(CompletionKind::Snippet as u8 == 16);
};

// MARK: - inlay hints, quick info

/// Bits of the `options` of `rln_inlay_hints`: Roslyn's inline hint check
/// boxes.
pub const RLN_INLAY_PARAMETERS: u32 = 1 << 0;
pub const RLN_INLAY_LITERAL_PARAMETERS: u32 = 1 << 1;
pub const RLN_INLAY_OBJECT_CREATION_PARAMETERS: u32 = 1 << 2;
pub const RLN_INLAY_OTHER_PARAMETERS: u32 = 1 << 3;
pub const RLN_INLAY_INDEXER_PARAMETERS: u32 = 1 << 4;
pub const RLN_INLAY_SUPPRESS_DIFFERING_BY_SUFFIX: u32 = 1 << 5;
pub const RLN_INLAY_SUPPRESS_MATCHING_METHOD_INTENT: u32 = 1 << 6;
pub const RLN_INLAY_SUPPRESS_MATCHING_ARGUMENT_NAME: u32 = 1 << 7;
pub const RLN_INLAY_TYPES: u32 = 1 << 8;
pub const RLN_INLAY_IMPLICIT_VARIABLE_TYPES: u32 = 1 << 9;
pub const RLN_INLAY_LAMBDA_PARAMETER_TYPES: u32 = 1 << 10;
pub const RLN_INLAY_IMPLICIT_OBJECT_CREATION: u32 = 1 << 11;

fn inlay_options(bits: u32) -> rustlyn_ide::semantic::InlayHintOptions {
    let on = |bit: u32| bits & bit != 0;
    rustlyn_ide::semantic::InlayHintOptions {
        parameters: on(RLN_INLAY_PARAMETERS),
        for_literal_parameters: on(RLN_INLAY_LITERAL_PARAMETERS),
        for_object_creation_parameters: on(RLN_INLAY_OBJECT_CREATION_PARAMETERS),
        for_other_parameters: on(RLN_INLAY_OTHER_PARAMETERS),
        for_indexer_parameters: on(RLN_INLAY_INDEXER_PARAMETERS),
        suppress_for_parameters_that_differ_only_by_suffix: on(
            RLN_INLAY_SUPPRESS_DIFFERING_BY_SUFFIX,
        ),
        suppress_for_parameters_that_match_method_intent: on(
            RLN_INLAY_SUPPRESS_MATCHING_METHOD_INTENT,
        ),
        suppress_for_parameters_that_match_argument_name: on(
            RLN_INLAY_SUPPRESS_MATCHING_ARGUMENT_NAME,
        ),
        types: on(RLN_INLAY_TYPES),
        for_implicit_variable_types: on(RLN_INLAY_IMPLICIT_VARIABLE_TYPES),
        for_lambda_parameter_types: on(RLN_INLAY_LAMBDA_PARAMETER_TYPES),
        for_implicit_object_creation: on(RLN_INLAY_IMPLICIT_OBJECT_CREATION),
    }
}

/// The options Roslyn shows once inline hints are turned on, as the bits
/// `rln_inlay_hints` takes.
#[unsafe(no_mangle)]
pub extern "C" fn rln_inlay_default_options() -> u32 {
    let defaults = rustlyn_ide::semantic::InlayHintOptions::default();
    [
        (defaults.parameters, RLN_INLAY_PARAMETERS),
        (
            defaults.for_literal_parameters,
            RLN_INLAY_LITERAL_PARAMETERS,
        ),
        (
            defaults.for_object_creation_parameters,
            RLN_INLAY_OBJECT_CREATION_PARAMETERS,
        ),
        (defaults.for_other_parameters, RLN_INLAY_OTHER_PARAMETERS),
        (
            defaults.for_indexer_parameters,
            RLN_INLAY_INDEXER_PARAMETERS,
        ),
        (
            defaults.suppress_for_parameters_that_differ_only_by_suffix,
            RLN_INLAY_SUPPRESS_DIFFERING_BY_SUFFIX,
        ),
        (
            defaults.suppress_for_parameters_that_match_method_intent,
            RLN_INLAY_SUPPRESS_MATCHING_METHOD_INTENT,
        ),
        (
            defaults.suppress_for_parameters_that_match_argument_name,
            RLN_INLAY_SUPPRESS_MATCHING_ARGUMENT_NAME,
        ),
        (defaults.types, RLN_INLAY_TYPES),
        (
            defaults.for_implicit_variable_types,
            RLN_INLAY_IMPLICIT_VARIABLE_TYPES,
        ),
        (
            defaults.for_lambda_parameter_types,
            RLN_INLAY_LAMBDA_PARAMETER_TYPES,
        ),
        (
            defaults.for_implicit_object_creation,
            RLN_INLAY_IMPLICIT_OBJECT_CREATION,
        ),
    ]
    .iter()
    .filter(|(on, _)| *on)
    .fold(0, |bits, (_, bit)| bits | bit)
}

/// One inlay hint, in UTF-16 code units.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnInlayHint {
    /// Drawn before the character here.
    pub position: u32,
    /// `count:` or `int`.
    pub label: RlnText,
    /// Where clicking it goes, when `flags` has `RLN_INLAY_HAS_TARGET`:
    /// relative to the project root, or an assembly's path.
    pub target_path: RlnText,
    pub target_line: u32,
    pub target_character: u32,
    /// What double-clicking it does, when `flags` has
    /// `RLN_INLAY_HAS_REPLACEMENT`: `replace_length` code units at
    /// `replace_start` of the file become `replace_text`.
    pub replace_start: u32,
    pub replace_length: u32,
    pub replace_text: RlnText,
    /// 0 a type, 1 a parameter name.
    pub kind: u8,
    /// `RLN_INLAY_PADDING_LEFT`, `RLN_INLAY_PADDING_RIGHT`,
    /// `RLN_INLAY_HAS_TARGET`, `RLN_INLAY_HAS_REPLACEMENT`.
    pub flags: u8,
}

/// Inlay hints. Freed with `rln_inlay_hints_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnInlayHints {
    pub items: *const RlnInlayHint,
    pub count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
}

/// The inlay hints for `start..end` (UTF-16) of the file, as `options`
/// (`RLN_INLAY_*` bits) allow. Free with `rln_inlay_hints_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_inlay_hints(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    start: u32,
    end: u32,
    options: u32,
    out: *mut RlnInlayHints,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        let options = inlay_options(options);
        match session
            .session
            .inlay_hints(path, start, end, text, &options)
        {
            Ok(found) => {
                let mut strings = Strings::default();
                let items: Vec<RlnInlayHint> = found
                    .iter()
                    .map(|hint| {
                        let mut flags =
                            u8::from(hint.padding_left) | (u8::from(hint.padding_right) << 1);
                        let mut item = RlnInlayHint {
                            position: hint.position,
                            label: strings.add(&hint.label),
                            kind: hint.kind as u8,
                            ..RlnInlayHint::default()
                        };
                        if let Some(target) = &hint.target {
                            flags |= 1 << 2;
                            item.target_path = strings.add(&target.path.to_string_lossy());
                            item.target_line = target.line;
                            item.target_character = target.character;
                        }
                        if let Some(change) = &hint.replacement {
                            flags |= 1 << 3;
                            item.replace_start = change.start;
                            item.replace_length = change.length;
                            item.replace_text = strings.add(&change.text);
                        }
                        item.flags = flags;
                        item
                    })
                    .collect();
                let (items, count) = leak(items);
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnInlayHints {
                        items,
                        count,
                        strings: bytes,
                        strings_length,
                    });
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_inlay_hints_free(hints: RlnInlayHints) {
    shallow((), || unsafe {
        reclaim(hints.items, hints.count);
        reclaim(hints.strings, hints.strings_length);
    });
}

/// What the mouse is on: Roslyn's quick info, in sections. Every text is
/// a slice of `strings`; an empty one is a section that is not there.
/// Freed with `rln_quick_info_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnQuickInfo {
    /// What it is about, UTF-16.
    pub start: u32,
    pub length: u32,
    /// `(local variable) int count`.
    pub description: RlnText,
    pub summary: RlnText,
    pub returns: RlnText,
    /// A property's `<value>`.
    pub value: RlnText,
    pub remarks: RlnText,
    /// The value known at compile time: `10`, `"count"`.
    pub constant: RlnText,
    /// Newline-separated: the exception types documented.
    pub exceptions: RlnText,
    /// Newline-separated: `T is int`.
    pub type_parameters: RlnText,
    /// Newline-separated: what a lambda or local function captures.
    pub captures: RlnText,
    pub parameters: *const RlnDocParameter,
    pub parameter_count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
}

/// The quick info for `offset` (UTF-16). Free with `rln_quick_info_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_quick_info(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnQuickInfo,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text)) =
            (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
                optional_text(text)
            })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.quick_info(path, offset, text) {
            Ok(found) => {
                let info = &found.info;
                let mut strings = Strings::default();
                let description = strings.add(&info.description);
                let summary = strings.add(&info.summary);
                let returns = strings.add(&info.returns);
                let value = strings.add(&info.value);
                let remarks = strings.add(&info.remarks);
                let constant = strings.add(info.constant.as_deref().unwrap_or(""));
                let exceptions = strings.add_list(&info.exceptions);
                let type_parameters = strings.add_list(&info.type_parameters);
                let captures = strings.add_list(&info.captures);
                let parameters: Vec<RlnDocParameter> = info
                    .parameters
                    .iter()
                    .map(|(name, text)| RlnDocParameter {
                        name: strings.add(name),
                        text: strings.add(text),
                    })
                    .collect();
                let (parameters, parameter_count) = leak(parameters);
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnQuickInfo {
                        start: found.start,
                        length: found.length,
                        description,
                        summary,
                        returns,
                        value,
                        remarks,
                        constant,
                        exceptions,
                        type_parameters,
                        captures,
                        parameters,
                        parameter_count,
                        strings: bytes,
                        strings_length,
                    });
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_quick_info_free(info: RlnQuickInfo) {
    shallow((), || unsafe {
        reclaim(info.parameters, info.parameter_count);
        reclaim(info.strings, info.strings_length);
    });
}

/// The sizes `include/rustlyn.h` states for the structs above.
const _: () = {
    assert!(size_of::<RlnInlayHint>() == 48);
};

// MARK: - .editorconfig, fix all, completion filtering

/// One `.editorconfig` setting: a lowercased key and its value as written.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnSetting {
    pub key: RlnText,
    pub value: RlnText,
}

/// The settings of a file. Freed with `rln_settings_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnSettings {
    pub items: *const RlnSetting,
    pub count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
}

/// Every `.editorconfig` setting that applies to `path`, keys sorted: what
/// the files from its directory up to a `root = true` one say, nearer ones
/// winning. Needs no compilation. Free with `rln_settings_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_editorconfig(
    session: *mut RlnSession,
    path: *const c_char,
    out: *mut RlnSettings,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path)) = (unsafe { held(session) }, unsafe { borrow(path) })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        let mut strings = Strings::default();
        let items: Vec<RlnSetting> = session
            .session
            .editorconfig(path)
            .iter()
            .map(|(key, value)| RlnSetting {
                key: strings.add(key),
                value: strings.add(value),
            })
            .collect();
        let (items, count) = leak(items);
        let (bytes, strings_length) = leak(strings.bytes);
        unsafe {
            out.write(RlnSettings {
                items,
                count,
                strings: bytes,
                strings_length,
            });
        }
        RlnStatus::Ok
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_settings_free(settings: RlnSettings) {
    shallow((), || unsafe {
        reclaim(settings.items, settings.count);
        reclaim(settings.strings, settings.strings_length);
    });
}

/// `scope` of `rln_fix_all`: the document asked about, or the project.
pub const RLN_FIX_ALL_DOCUMENT: u8 = 0;
pub const RLN_FIX_ALL_PROJECT: u8 = 1;

/// Fix All: the fix for diagnostic `code` (`CS0168`, `IDE0005`, `IDE1006`)
/// applied to every occurrence of it in the document or, with
/// `RLN_FIX_ALL_PROJECT`, the project, as one set of edits. Needs a
/// compilation. Free with `rln_edits_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_fix_all(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    code: *const c_char,
    scope: u8,
    out: *mut RlnEdits,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path), Ok(text), Some(code)) = (
            unsafe { held(session) },
            unsafe { borrow(path) },
            unsafe { optional_text(text) },
            unsafe { borrow(code) },
        ) else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() || scope > RLN_FIX_ALL_PROJECT {
            return RlnStatus::BadArgument;
        }
        let scope = if scope == RLN_FIX_ALL_PROJECT {
            rustlyn_ide::semantic::FixAllScope::Project
        } else {
            rustlyn_ide::semantic::FixAllScope::Document
        };
        match session.session.fix_all(path, code, scope, text) {
            Ok(changes) => {
                unsafe { write_edits(out, &changes) };
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

/// One completion item that matched, in Roslyn's order: its position in the
/// names asked about, how it matched (`RLN_MATCH_*`), and whether the case
/// matched too.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnFilteredItem {
    pub index: u32,
    pub kind: u8,
    pub case_sensitive: u8,
}

/// The items that matched. Freed with `rln_filtered_items_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnFilteredItems {
    pub items: *const RlnFilteredItem,
    pub count: usize,
}

/// Filters and orders `count` completion names — each item's filter text,
/// or its label — by what has been `typed`, as Roslyn's pattern matcher
/// does: exact, then prefix, then word starts and camel humps, then
/// substrings and near misses; letters in the typed case before others.
/// Needs no session. Free with `rln_filtered_items_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_completion_filter(
    names: *const *const c_char,
    count: usize,
    typed: *const c_char,
    out: *mut RlnFilteredItems,
) -> RlnStatus {
    shallow(RlnStatus::Panicked, || {
        if out.is_null() || (names.is_null() && count > 0) {
            return RlnStatus::BadArgument;
        }
        let typed = unsafe { borrow(typed) }.unwrap_or("");
        let mut owned: Vec<&str> = Vec::with_capacity(count);
        for index in 0..count {
            let Some(name) = (unsafe { borrow(*names.add(index)) }) else {
                return RlnStatus::BadArgument;
            };
            owned.push(name);
        }
        let mut found = rustlyn_ide::session::filter_names(&owned, typed);
        found.sort_by(|a, b| {
            a.kind
                .cmp(&b.kind)
                .then(b.case_sensitive.cmp(&a.case_sensitive))
                .then(owned[a.index].len().cmp(&owned[b.index].len()))
                .then(a.index.cmp(&b.index))
        });
        let items: Vec<RlnFilteredItem> = found
            .iter()
            .map(|item| RlnFilteredItem {
                index: item.index as u32,
                kind: item.kind as u8,
                case_sensitive: u8::from(item.case_sensitive),
            })
            .collect();
        let (items, count) = leak(items);
        unsafe { out.write(RlnFilteredItems { items, count }) };
        RlnStatus::Ok
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_filtered_items_free(items: RlnFilteredItems) {
    shallow((), || unsafe { reclaim(items.items, items.count) });
}

/// The sizes `include/rustlyn.h` states for the structs above.
const _: () = {
    assert!(size_of::<RlnSetting>() == 16);
    assert!(size_of::<RlnFilteredItem>() == 8);
};

// MARK: - layer 5

/// An assembly's surface as C#. Free the text with `rln_text_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_assembly_text(
    session: *mut RlnSession,
    path: *const c_char,
    out: *mut RlnString,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path)) = (unsafe { held(session) }, unsafe { borrow(path) })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.assembly(path) {
            Ok(surface) => {
                let (bytes, length) = leak(surface.text.clone().into_bytes());
                unsafe { out.write(RlnString { bytes, length }) };
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

/// The metadata token of the declaration at `line` in an assembly's rendered
/// text, so a body can be asked for.
///
/// Returns zero when there is no declaration on that line, which is not an
/// error: most lines have none.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_assembly_token_at_line(
    session: *mut RlnSession,
    path: *const c_char,
    line: u32,
) -> u32 {
    guard(0, || {
        let (Some(session), Some(path)) = (unsafe { held(session) }, unsafe { borrow(path) })
        else {
            return 0;
        };
        let Ok(surface) = session.session.assembly(path) else {
            return 0;
        };
        surface
            .declarations
            .iter()
            .find(|declaration| declaration.line == line && !declaration.is_type)
            .map_or(0, |declaration| declaration.token)
    })
}

/// One method's IL. Free the text with `rln_text_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_method_body(
    session: *mut RlnSession,
    path: *const c_char,
    token: u32,
    out: *mut RlnString,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some(session), Some(path)) = (unsafe { held(session) }, unsafe { borrow(path) })
        else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session.session.method_body(path, token) {
            Ok(body) => {
                let (bytes, length) = leak(body.text.clone().into_bytes());
                unsafe { out.write(RlnString { bytes, length }) };
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

/// The number of declaration kinds, so a caller can check its own table
/// against this build rather than trusting that they still line up.
#[unsafe(no_mangle)]
pub extern "C" fn rln_declaration_kind_count() -> u32 {
    DeclarationKind::Extension as u32 + 1
}

/// The number of colour classes, for the same reason.
#[unsafe(no_mangle)]
pub extern "C" fn rln_class_count() -> u32 {
    rustlyn_ide::Class::Disabled as u32 + 1
}

/// The sizes `include/rustlyn.h` states.
///
/// The header is written by hand and its C test checks these same numbers
/// from the other side. Stating them here too means a field added to one of
/// these structs breaks this build rather than silently changing a layout
/// that something else is reading by offset.
const _: () = {
    assert!(size_of::<RlnText>() == 8);
    assert!(size_of::<RlnRun>() == 12);
    assert!(size_of::<RlnDeclaration>() == 92);
    assert!(size_of::<RlnLocation>() == 32);
    assert!(size_of::<RlnCompletion>() == 20);
    assert!(size_of::<RlnCompiled>() == 40);
    assert!(size_of::<RlnRange>() == 8);
    assert!(size_of::<RlnDiagnostic>() == 28);
    assert!(size_of::<RlnSignature>() == 16);
    assert!(size_of::<RlnDocParameter>() == 16);
    assert!(size_of::<RlnEdit>() == 24);
    assert!(size_of::<RlnRename>() == 16);
    assert!(size_of::<RlnCodeAction>() == 36);
};

// MARK: - hot reload

/// A string for JSON.
fn json_text(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for character in text.chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn json_owned(json: String) -> RlnString {
    let (bytes, length) = leak(json.into_bytes());
    RlnString { bytes, length }
}

fn built_json(built: Result<rustlyn_ide::hot::Built, String>) -> String {
    match built {
        Ok(built) => format!(
            "{{\"ok\":true,\"assembly\":{},\"milliseconds\":{},\"stubs\":{}}}",
            json_text(&built.assembly.to_string_lossy()),
            built.milliseconds,
            built.stubs
        ),
        Err(why) => format!("{{\"ok\":false,\"error\":{}}}", json_text(&why)),
    }
}

/// Starts hot reload for a Unity project: runs every source generator over
/// Assembly-CSharp, compiles the project with what they wrote, and builds
/// the Assembly-CSharp an editor is to load (`assembly` in the answer).
/// `tools` is JSON: {"dotnet", "gend", "minigen", "runtime"} paths. `paths`
/// are as for rln_compile. Blocks for tens of seconds. Answers JSON
/// {"ok":true,"assembly","milliseconds","stubs"} or {"ok":false,"error"};
/// free with rln_text_free.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_hot_start(
    session: *mut RlnSession,
    tools: *const c_char,
    paths: *const *const c_char,
    count: usize,
) -> RlnString {
    guard(
        json_owned("{\"ok\":false,\"error\":\"panicked\"}".into()),
        || {
            let (Some(session), Some(tools), Some(list)) =
                (unsafe { held(session) }, unsafe { borrow(tools) }, unsafe {
                    path_list(paths, count)
                })
            else {
                return json_owned("{\"ok\":false,\"error\":\"bad argument\"}".into());
            };
            let field = |name: &str| -> PathBuf {
                let key = format!("\"{name}\"");
                tools
                    .find(&key)
                    .and_then(|at| tools[at + key.len()..].split('"').nth(1))
                    // JSON may escape the slashes of a path.
                    .map(|path| PathBuf::from(path.replace("\\/", "/")))
                    .unwrap_or_default()
            };
            let tools = rustlyn_ide::hot::Tools {
                dotnet: field("dotnet"),
                gend: field("gend"),
                minigen: field("minigen"),
                runtime: field("runtime"),
            };
            json_owned(built_json(session.session.hot_start(tools, &list)))
        },
    )
}

/// What saving `saved` comes to under hot reload: the generators run over
/// them, the project compiled, the patch made. Answers JSON with "kind":
/// "patch" (with "assembly", the patch to send the editor, and "methods",
/// what it replaces), "unchanged", "broken" (with "reason": the file does
/// not compile yet), "reload" (with "reason": only rln_hot_rebuild and a
/// reload carry it), "outside" (not a file of Assembly-CSharp), or "error";
/// and "milliseconds". Free with rln_text_free.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_hot_save(
    session: *mut RlnSession,
    saved: *const *const c_char,
    saved_count: usize,
    paths: *const *const c_char,
    count: usize,
) -> RlnString {
    guard(
        json_owned("{\"kind\":\"error\",\"reason\":\"panicked\"}".into()),
        || {
            let (Some(session), Some(saved), Some(list)) = (
                unsafe { held(session) },
                unsafe { path_list(saved, saved_count) },
                unsafe { path_list(paths, count) },
            ) else {
                return json_owned("{\"kind\":\"error\",\"reason\":\"bad argument\"}".into());
            };
            let started = std::time::Instant::now();
            let answer = session.session.hot_save(&saved, &list);
            let milliseconds = started.elapsed().as_millis();
            use rustlyn_ide::hot::Answer;
            let json = match answer {
                Ok(Answer::Patch { assembly, methods }) => format!(
                    "{{\"kind\":\"patch\",\"assembly\":{},\"methods\":[{}],\"milliseconds\":{milliseconds}}}",
                    json_text(&assembly.to_string_lossy()),
                    methods
                        .iter()
                        .map(|method| json_text(method))
                        .collect::<Vec<_>>()
                        .join(",")
                ),
                Ok(Answer::Unchanged) => {
                    format!("{{\"kind\":\"unchanged\",\"milliseconds\":{milliseconds}}}")
                }
                Ok(Answer::Broken(why)) => {
                    format!(
                        "{{\"kind\":\"broken\",\"reason\":{},\"milliseconds\":{milliseconds}}}",
                        json_text(&why)
                    )
                }
                Ok(Answer::Reload(why)) => {
                    format!(
                        "{{\"kind\":\"reload\",\"reason\":{},\"milliseconds\":{milliseconds}}}",
                        json_text(&why)
                    )
                }
                Ok(Answer::Outside) => {
                    format!("{{\"kind\":\"outside\",\"milliseconds\":{milliseconds}}}")
                }
                Err(why) => format!(
                    "{{\"kind\":\"error\",\"reason\":{},\"milliseconds\":{milliseconds}}}",
                    json_text(&why)
                ),
            };
            json_owned(json)
        },
    )
}

/// The text of the file at `path` as the build the editor runs has it — what
/// an edit made outside the IDE was before — as JSON {"text": …}, or {} for
/// a file that build does not have. Free with rln_text_free.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_hot_base_text(
    session: *mut RlnSession,
    path: *const *const c_char,
) -> RlnString {
    guard(json_owned("{}".into()), || {
        let (Some(session), Some(list)) = (unsafe { held(session) }, unsafe { path_list(path, 1) })
        else {
            return json_owned("{}".into());
        };
        match list
            .first()
            .and_then(|path| session.session.hot_base_text(path))
        {
            Some(text) => json_owned(format!("{{\"text\":{}}}", json_text(&text))),
            None => json_owned("{}".into()),
        }
    })
}

/// A whole build for the editor to reload on, of the files as they are
/// now; after the editor loaded it, patches are measured against it.
/// Answers as rln_hot_start.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_hot_rebuild(
    session: *mut RlnSession,
    paths: *const *const c_char,
    count: usize,
) -> RlnString {
    guard(
        json_owned("{\"ok\":false,\"error\":\"panicked\"}".into()),
        || {
            let (Some(session), Some(list)) =
                (unsafe { held(session) }, unsafe { path_list(paths, count) })
            else {
                return json_owned("{\"ok\":false,\"error\":\"bad argument\"}".into());
            };
            json_owned(built_json(session.session.hot_rebuild(&list)))
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;

    struct TempDir(PathBuf);

    impl TempDir {
        fn new(name: &str) -> Self {
            let path = std::env::temp_dir().join(format!(
                "rustlyn-ffi-{name}-{}-{:?}",
                std::process::id(),
                std::thread::current().id()
            ));
            let _ = std::fs::remove_dir_all(&path);
            std::fs::create_dir_all(&path).expect("a temporary directory");
            Self(path)
        }
        fn write(&self, name: &str, text: &str) -> CString {
            let path = self.0.join(name);
            std::fs::write(&path, text).expect("writing");
            CString::new(path.to_string_lossy().as_bytes()).expect("a path with no NUL")
        }
        fn root(&self) -> CString {
            CString::new(self.0.to_string_lossy().as_bytes()).expect("a path with no NUL")
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn open_session(dir: &TempDir) -> *mut RlnSession {
        let session =
            unsafe { rln_session_new(dir.root().as_ptr(), std::ptr::null(), std::ptr::null(), 0) };
        assert!(!session.is_null());
        session
    }

    /// The bytes a `RlnText` names, out of a result's blob.
    unsafe fn text_of(strings: *const u8, length: usize, slice: RlnText) -> String {
        let blob = unsafe { std::slice::from_raw_parts(strings, length) };
        String::from_utf8_lossy(
            &blob[slice.offset as usize..(slice.offset + slice.length) as usize],
        )
        .into_owned()
    }

    #[test]
    fn a_session_opens_and_closes() {
        let dir = TempDir::new("session");
        let session = open_session(&dir);
        unsafe { rln_session_free(session) };
    }

    #[test]
    fn freeing_a_null_session_is_allowed() {
        unsafe { rln_session_free(std::ptr::null_mut()) };
    }

    #[test]
    fn a_null_root_gives_a_null_session_rather_than_a_crash() {
        let session =
            unsafe { rln_session_new(std::ptr::null(), std::ptr::null(), std::ptr::null(), 0) };
        assert!(session.is_null());
    }

    #[test]
    fn every_call_refuses_a_null_session_rather_than_dereferencing_it() {
        let null = std::ptr::null_mut();
        let path = CString::new("/nowhere/A.cs").expect("a path");
        unsafe {
            assert_eq!(rln_open(null, path.as_ptr()), RlnStatus::BadArgument);
            assert_eq!(
                rln_classify(null, path.as_ptr(), 0, 0, std::ptr::null_mut()),
                RlnStatus::BadArgument,
            );
            assert_eq!(
                rln_outline(null, path.as_ptr(), std::ptr::null_mut()),
                RlnStatus::BadArgument,
            );
            assert_eq!(
                rln_definition(null, path.as_ptr(), 0, std::ptr::null_mut()),
                RlnStatus::BadArgument,
            );
            assert_eq!(rln_warm(null, path.as_ptr()), RlnStatus::BadArgument);
            // And these must simply not crash.
            rln_close(null, path.as_ptr());
            assert_eq!(rln_assembly_token_at_line(null, path.as_ptr(), 0), 0);
        }
    }

    #[test]
    fn a_null_path_is_a_bad_argument_rather_than_a_crash() {
        let dir = TempDir::new("nullpath");
        let session = open_session(&dir);
        unsafe {
            assert_eq!(rln_open(session, std::ptr::null()), RlnStatus::BadArgument);
            assert_eq!(
                rln_set_text(session, std::ptr::null(), std::ptr::null()),
                RlnStatus::BadArgument,
            );
            rln_session_free(session);
        }
    }

    #[test]
    fn opening_a_file_that_is_not_there_reports_why() {
        let dir = TempDir::new("missing");
        let session = open_session(&dir);
        let path = CString::new(dir.0.join("Gone.cs").to_string_lossy().as_bytes()).expect("path");
        unsafe {
            assert_eq!(rln_open(session, path.as_ptr()), RlnStatus::Io);
            let message = rln_last_error(session);
            assert!(message.length > 0, "the reason should be readable");
            rln_text_free(message);
            rln_session_free(session);
        }
    }

    #[test]
    fn colouring_comes_back_as_runs_and_frees_cleanly() {
        let dir = TempDir::new("classify");
        let path = dir.write("A.cs", "public class A { }\n");
        let session = open_session(&dir);
        unsafe {
            assert_eq!(rln_open(session, path.as_ptr()), RlnStatus::Ok);
            let mut runs = RlnRuns {
                items: std::ptr::null(),
                count: 0,
            };
            assert_eq!(
                rln_classify(session, path.as_ptr(), 0, 0, &raw mut runs),
                RlnStatus::Ok,
            );
            assert!(runs.count > 0);
            let items = std::slice::from_raw_parts(runs.items, runs.count);
            assert!(
                items
                    .iter()
                    .any(|run| run.class == rustlyn_ide::Class::Keyword as u8)
            );
            rln_runs_free(runs);
            rln_session_free(session);
        }
    }

    #[test]
    fn colouring_a_file_that_is_not_csharp_says_so() {
        let dir = TempDir::new("notcs");
        let path = dir.write("main.rs", "fn main() {}\n");
        let session = open_session(&dir);
        unsafe {
            assert_eq!(rln_open(session, path.as_ptr()), RlnStatus::Ok);
            let mut runs = RlnRuns {
                items: std::ptr::null(),
                count: 0,
            };
            assert_eq!(
                rln_classify(session, path.as_ptr(), 0, 0, &raw mut runs),
                RlnStatus::NotCsharp,
            );
            rln_session_free(session);
        }
    }

    #[test]
    fn an_outline_comes_back_with_its_strings_in_one_blob() {
        let dir = TempDir::new("outline");
        let path = dir.write(
            "A.cs",
            "using System;\nnamespace Game;\n[Serializable] public class Pawn : Base {\n  public int Damage(int n, string why) { return n; }\n}\n",
        );
        let session = open_session(&dir);
        unsafe {
            assert_eq!(rln_open(session, path.as_ptr()), RlnStatus::Ok);
            let mut outline = std::mem::zeroed::<RlnOutline>();
            assert_eq!(
                rln_outline(session, path.as_ptr(), &raw mut outline),
                RlnStatus::Ok,
            );
            // The namespace, the class and the method: an outline view shows
            // the namespace too, which the project index does not keep.
            assert_eq!(outline.count, 3);

            let declarations = std::slice::from_raw_parts(outline.declarations, outline.count);
            let name = |slice| text_of(outline.strings, outline.strings_length, slice);
            let find = |wanted: &str| {
                declarations
                    .iter()
                    .find(|declaration| name(declaration.name) == wanted)
                    .unwrap_or_else(|| panic!("no declaration named {wanted}"))
            };

            let pawn = find("Pawn");
            assert_eq!(name(pawn.name), "Pawn");
            assert_eq!(name(pawn.keyword), "class");
            assert_eq!(name(pawn.bases), "Base");
            assert_eq!(name(pawn.attributes), "Serializable");
            assert_eq!(name(pawn.container), "Game");

            let damage = find("Damage");
            assert_eq!(name(damage.name), "Damage");
            assert_eq!(name(damage.type_text), "int");
            assert_eq!(damage.parameter_count, 2);
            assert_eq!(name(damage.parameters), "int n\nstring why");

            assert_eq!(name(outline.namespaces), "Game");
            assert_eq!(name(outline.usings), "System");

            rln_outline_free(outline);
            rln_session_free(session);
        }
    }

    #[test]
    fn an_outlines_spans_are_utf16_and_land_on_the_name() {
        let dir = TempDir::new("outlineutf16");
        let text = "// комментарий\nclass Pawn { }\n";
        let path = dir.write("A.cs", text);
        let session = open_session(&dir);
        unsafe {
            assert_eq!(rln_open(session, path.as_ptr()), RlnStatus::Ok);
            let mut outline = std::mem::zeroed::<RlnOutline>();
            assert_eq!(
                rln_outline(session, path.as_ptr(), &raw mut outline),
                RlnStatus::Ok,
            );
            let declarations = std::slice::from_raw_parts(outline.declarations, outline.count);
            let units: Vec<u16> = text.encode_utf16().collect();
            let pawn = &declarations[0];
            let found = String::from_utf16_lossy(
                &units[pawn.name_start as usize..(pawn.name_start + pawn.name_length) as usize],
            );
            assert_eq!(found, "Pawn");
            rln_outline_free(outline);
            rln_session_free(session);
        }
    }

    #[test]
    fn going_to_a_definition_across_the_boundary() {
        let dir = TempDir::new("goto");
        let pawn = dir.write(
            "Pawn.cs",
            "namespace Game;\nclass Pawn { public int Health; }\n",
        );
        let use_text = "namespace Game;\nclass Use { void M(Pawn p) { var n = p.Health; } }\n";
        let use_path = dir.write("Use.cs", use_text);
        let session = open_session(&dir);
        unsafe {
            let paths = [pawn.as_ptr(), use_path.as_ptr()];
            let mut report = RlnReport::default();
            assert_eq!(
                rln_reindex(session, paths.as_ptr(), 2, &raw mut report),
                RlnStatus::Ok,
            );
            assert_eq!(report.parsed, 2);

            assert_eq!(rln_open(session, use_path.as_ptr()), RlnStatus::Ok);
            let offset = use_text.find("Health").expect("Health") as u32;

            let mut locations = std::mem::zeroed::<RlnLocations>();
            assert_eq!(
                rln_definition(session, use_path.as_ptr(), offset, &raw mut locations),
                RlnStatus::Ok,
            );
            assert!(locations.certain);
            assert_eq!(locations.count, 1);
            let items = std::slice::from_raw_parts(locations.items, locations.count);
            let read = |slice| text_of(locations.strings, locations.strings_length, slice);
            assert_eq!(read(locations.word), "Health");
            assert_eq!(read(items[0].path), "Pawn.cs");
            assert_eq!(read(items[0].name), "Game.Pawn.Health");
            assert_eq!(items[0].line, 1);

            rln_locations_free(locations);
            rln_session_free(session);
        }
    }

    #[test]
    fn a_cursor_on_nothing_comes_back_as_a_status_and_a_reason() {
        let dir = TempDir::new("notaname");
        let path = dir.write("A.cs", "class A { void M() { } }");
        let session = open_session(&dir);
        unsafe {
            let paths = [path.as_ptr()];
            assert_eq!(
                rln_reindex(session, paths.as_ptr(), 1, std::ptr::null_mut()),
                RlnStatus::Ok,
            );
            assert_eq!(rln_open(session, path.as_ptr()), RlnStatus::Ok);
            let mut locations = std::mem::zeroed::<RlnLocations>();
            assert_eq!(
                rln_definition(session, path.as_ptr(), 0, &raw mut locations),
                RlnStatus::NotAName,
            );
            let message = rln_last_error(session);
            assert!(message.length > 0);
            rln_text_free(message);
            rln_session_free(session);
        }
    }

    #[test]
    fn an_assembly_that_is_not_one_comes_back_as_a_status() {
        let dir = TempDir::new("notdll");
        let path = dir.write("fake.dll", "not a PE image at all");
        let session = open_session(&dir);
        unsafe {
            let mut text = RlnString {
                bytes: std::ptr::null(),
                length: 0,
            };
            assert_eq!(
                rln_assembly_text(session, path.as_ptr(), &raw mut text),
                RlnStatus::Assembly,
            );
            rln_session_free(session);
        }
    }

    #[test]
    fn an_empty_result_frees_without_incident() {
        // A zero-length vector's pointer is dangling rather than null, and
        // handing it back has to be a no-op rather than a free of nothing.
        unsafe {
            rln_runs_free(RlnRuns {
                items: std::ptr::null(),
                count: 0,
            });
            rln_text_free(RlnString {
                bytes: std::ptr::null(),
                length: 0,
            });
            rln_locations_free(std::mem::zeroed::<RlnLocations>());
            rln_outline_free(std::mem::zeroed::<RlnOutline>());
        }
    }

    #[test]
    fn the_counts_a_caller_checks_itself_against_are_right() {
        // A Swift or C caller mirrors these enums by hand. If one grows here
        // and not there, this is what tells them.
        assert_eq!(rln_declaration_kind_count(), 17);
        assert_eq!(rln_class_count(), 15);
    }

    #[test]
    fn a_session_answers_from_several_threads_at_once() {
        let dir = TempDir::new("threads");
        let mut paths = Vec::new();
        for n in 0..20 {
            paths.push(dir.write(
                &format!("F{n}.cs"),
                &format!("class T{n} {{ void M() {{ }} }}"),
            ));
        }
        let session = open_session(&dir);
        let pointers: Vec<*const c_char> = paths.iter().map(|path| path.as_ptr()).collect();
        unsafe {
            assert_eq!(
                rln_reindex(
                    session,
                    pointers.as_ptr(),
                    pointers.len(),
                    std::ptr::null_mut()
                ),
                RlnStatus::Ok,
            );
        }

        // A raw pointer is not `Send`, so say out loud that this one is: the
        // session behind it is, and that is what the threads touch.
        struct Shared(*mut RlnSession);
        unsafe impl Send for Shared {}
        unsafe impl Sync for Shared {}
        let shared = Shared(session);

        std::thread::scope(|scope| {
            for path in &paths {
                let shared = &shared;
                scope.spawn(move || unsafe {
                    assert_eq!(rln_open(shared.0, path.as_ptr()), RlnStatus::Ok);
                    let mut runs = RlnRuns {
                        items: std::ptr::null(),
                        count: 0,
                    };
                    assert_eq!(
                        rln_classify(shared.0, path.as_ptr(), 0, 10, &raw mut runs),
                        RlnStatus::Ok,
                    );
                    rln_runs_free(runs);

                    let mut outline = std::mem::zeroed::<RlnOutline>();
                    assert_eq!(
                        rln_outline(shared.0, path.as_ptr(), &raw mut outline),
                        RlnStatus::Ok,
                    );
                    rln_outline_free(outline);
                });
            }
        });
        unsafe { rln_session_free(session) };
    }

    // MARK: - code fixes

    #[test]
    fn a_missing_using_comes_back_as_a_fix_with_its_edit() {
        let dir = TempDir::new("fixes");
        let tools = dir.write(
            "Tools.cs",
            "namespace Game.Tools;\npublic class Hammer { }\n",
        );
        let use_text = "namespace Game;\nclass Use { Hammer tool; }\n";
        let use_path = dir.write("Use.cs", use_text);
        let session = open_session(&dir);
        unsafe {
            let paths = [tools.as_ptr(), use_path.as_ptr()];
            assert_eq!(
                rln_compile(session, paths.as_ptr(), 2, std::ptr::null_mut()),
                RlnStatus::Ok,
            );
            assert_eq!(rln_open(session, use_path.as_ptr()), RlnStatus::Ok);
            let offset = use_text.find("Hammer").expect("Hammer") as u32;
            let mut actions = std::mem::zeroed::<RlnCodeActions>();
            assert_eq!(
                rln_code_actions(
                    session,
                    use_path.as_ptr(),
                    std::ptr::null(),
                    offset,
                    offset,
                    &raw mut actions,
                ),
                RlnStatus::Ok,
            );
            let items = std::slice::from_raw_parts(actions.items, actions.count);
            let edits = std::slice::from_raw_parts(actions.edits, actions.edit_count);
            let read = |slice| text_of(actions.strings, actions.strings_length, slice);
            let using = items
                .iter()
                .find(|item| read(item.title) == "using Game.Tools;")
                .expect("the using is offered");
            assert_eq!(read(using.fixes), "CS0246");
            assert_eq!(
                using.kind,
                rustlyn_ide::semantic::ActionKind::QuickFix as u8
            );
            assert_eq!(using.edit_count, 1);
            let edit = &edits[using.first_edit as usize];
            assert_eq!(read(edit.text), "using Game.Tools;\n\n");
            assert_eq!(edit.start, 0);
            assert!(read(edit.path).ends_with("Use.cs"));
            rln_code_actions_free(actions);
            rln_session_free(session);
        }
    }

    // MARK: - a deep file on a small stack

    #[test]
    fn a_file_nested_nine_thousand_deep_is_answered_on_a_small_stack() {
        // What a request reads is walked as deep as the tree is, which an
        // unoptimized build needs more stack for than an editor's thread
        // has. The work is done on a stack made for it, so the answer comes
        // back whichever thread asked.
        let dir = TempDir::new("deep");
        let text = format!(
            "class C {{ int M(int a) => {}0; }}\n",
            (0..9000)
                .map(|i| format!("a == {i} ? {i} : "))
                .collect::<String>()
        );
        let path = dir.write("C.cs", &text);
        let root = dir.root();
        let content = CString::new(text.as_bytes()).expect("text with no NUL");
        let length = text.len() as u32;
        let small = std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(move || unsafe {
                let session = rln_session_new(root.as_ptr(), std::ptr::null(), std::ptr::null(), 0);
                assert!(!session.is_null());
                assert_eq!(
                    rln_open_text(session, path.as_ptr(), content.as_ptr()),
                    RlnStatus::Ok
                );
                let paths = [path.as_ptr()];
                assert_eq!(
                    rln_compile(session, paths.as_ptr(), 1, std::ptr::null_mut()),
                    RlnStatus::Ok,
                );

                let mut diagnostics = std::mem::zeroed::<RlnDiagnostics>();
                assert_eq!(
                    rln_diagnostics(
                        session,
                        path.as_ptr(),
                        content.as_ptr(),
                        &raw mut diagnostics
                    ),
                    RlnStatus::Ok,
                );
                rln_diagnostics_free(diagnostics);

                let mut runs = std::mem::zeroed::<RlnSemanticRuns>();
                assert_eq!(
                    rln_semantic_tokens(
                        session,
                        path.as_ptr(),
                        content.as_ptr(),
                        0,
                        length,
                        &raw mut runs
                    ),
                    RlnStatus::Ok,
                );
                assert!(runs.count > 9000);
                rln_semantic_runs_free(runs);

                let mut actions = std::mem::zeroed::<RlnCodeActions>();
                assert_eq!(
                    rln_code_actions(
                        session,
                        path.as_ptr(),
                        content.as_ptr(),
                        length / 2,
                        length / 2,
                        &raw mut actions,
                    ),
                    RlnStatus::Ok,
                );
                rln_code_actions_free(actions);
                rln_session_free(session);
            })
            .expect("a thread");
        small.join().expect("no overflow");
    }
}
