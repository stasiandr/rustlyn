//! The syntax-level editing services across the boundary: formatting,
//! smart indentation, block structure, brace matching, documentation
//! snippets and comment toggling. None of them needs a compilation.
//!
//! The conventions are the rest of the library's: every entry point is
//! guarded, every result has its free, strings travel in one blob beside
//! the items that point into it, and offsets are UTF-16.

use std::ffi::c_char;

use rustlyn_ide::session::Changes;
use rustlyn_ide::session::editing::Snippet;
use rustlyn_ide::structure::{FoldKind, StructureOptions};

use super::{
    RlnEdits, RlnSession, RlnStatus, RlnString, RlnText, Strings, borrow, guard, held, leak,
    optional_text, reclaim, shallow, write_edits,
};

/// One foldable block. `banner` is a slice of the result's `strings`.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnFoldingRange {
    /// What folds away.
    pub start: u32,
    pub end: u32,
    /// The whole construct, for a tooltip.
    pub hint_start: u32,
    pub hint_end: u32,
    /// What stands in for the folded text.
    pub banner: RlnText,
    /// A `FoldKind`, as its discriminant.
    pub kind: u8,
    pub collapsible: bool,
    pub collapsed_by_default: bool,
}

/// A file's foldable blocks. Freed with `rln_folding_ranges_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnFoldingRanges {
    pub items: *const RlnFoldingRange,
    pub count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
}

/// Two delimiters that belong together; all zero and `found` false when
/// the caret is beside none.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnBracePair {
    pub open_start: u32,
    pub open_end: u32,
    pub close_start: u32,
    pub close_end: u32,
    pub found: bool,
}

/// Documentation to write, and the caret after writing it (UTF-16, in the
/// text once the edits are applied). Empty and `found` false when there is
/// nothing to write. Freed with `rln_snippet_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnSnippet {
    pub edits: RlnEdits,
    pub caret: u32,
    pub found: bool,
}

/// The session, path and optional text every call here takes, or the
/// status that says which of them was bad.
unsafe fn arguments<'a>(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    out_is_null: bool,
) -> Result<(&'a RlnSession, &'a str, Option<&'a str>), RlnStatus> {
    let (Some(session), Some(path), Ok(text)) =
        (unsafe { held(session) }, unsafe { borrow(path) }, unsafe {
            optional_text(text)
        })
    else {
        return Err(RlnStatus::BadArgument);
    };
    if out_is_null {
        return Err(RlnStatus::BadArgument);
    }
    Ok((session, path, text))
}

/// Hands edits to C, or the refusal's status.
unsafe fn answer_edits(
    session: &RlnSession,
    found: Result<Changes, rustlyn_ide::session::Refusal>,
    out: *mut RlnEdits,
) -> RlnStatus {
    match found {
        Ok(changes) => {
            unsafe { write_edits(out, &changes) };
            RlnStatus::Ok
        }
        Err(refusal) => session.note(&refusal),
    }
}

/// The edits that format the whole file. Free with `rln_edits_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_format_document(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    out: *mut RlnEdits,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        match unsafe { arguments(session, path, text, out.is_null()) } {
            Ok((session, path, text)) => unsafe {
                answer_edits(session, session.session.format_document(path, text), out)
            },
            Err(status) => status,
        }
    })
}

/// The edits that format the lines `start..end` (UTF-16) touches. Free
/// with `rln_edits_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_format_range(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    start: u32,
    end: u32,
    out: *mut RlnEdits,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        match unsafe { arguments(session, path, text, out.is_null()) } {
            Ok((session, path, text)) => unsafe {
                answer_edits(
                    session,
                    session.session.format_range(path, start, end, text),
                    out,
                )
            },
            Err(status) => status,
        }
    })
}

/// What typing `typed` (a Unicode scalar) reformats, with `position` the
/// caret just after it. Free with `rln_edits_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_format_on_type(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    position: u32,
    typed: u32,
    out: *mut RlnEdits,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let Some(typed) = char::from_u32(typed) else {
            return RlnStatus::BadArgument;
        };
        match unsafe { arguments(session, path, text, out.is_null()) } {
            Ok((session, path, text)) => unsafe {
                answer_edits(
                    session,
                    session.session.format_on_type(path, position, typed, text),
                    out,
                )
            },
            Err(status) => status,
        }
    })
}

/// The indentation for a new line when Enter is pressed at `position`.
/// `bytes` is null when there is no opinion (inside a string over several
/// lines); an empty, non-null text is the first column. Free with
/// `rln_text_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_indentation_for_new_line(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    position: u32,
    out: *mut RlnString,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (session, path, text) = match unsafe { arguments(session, path, text, out.is_null()) } {
            Ok(arguments) => arguments,
            Err(status) => return status,
        };
        match session
            .session
            .indentation_for_new_line(path, position, text)
        {
            Ok(Some(indentation)) => {
                let (bytes, length) = leak(indentation.into_bytes());
                unsafe { out.write(RlnString { bytes, length }) };
                RlnStatus::Ok
            }
            Ok(None) => {
                unsafe {
                    out.write(RlnString {
                        bytes: std::ptr::null(),
                        length: 0,
                    });
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

/// Every foldable block of the file. `collapse_usings` makes the `using`
/// directives start folded; regions always do. Free with
/// `rln_folding_ranges_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_block_structure(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    collapse_usings: bool,
    out: *mut RlnFoldingRanges,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (session, path, text) = match unsafe { arguments(session, path, text, out.is_null()) } {
            Ok(arguments) => arguments,
            Err(status) => return status,
        };
        let options = StructureOptions {
            collapse_imports: collapse_usings,
            ..StructureOptions::default()
        };
        match session.session.block_structure(path, text, options) {
            Ok(folds) => {
                let mut strings = Strings::default();
                let items: Vec<RlnFoldingRange> = folds
                    .iter()
                    .map(|fold| RlnFoldingRange {
                        start: fold.start,
                        end: fold.end,
                        hint_start: fold.hint_start,
                        hint_end: fold.hint_end,
                        banner: strings.add(&fold.banner),
                        kind: fold.kind as u8,
                        collapsible: fold.collapsible,
                        collapsed_by_default: fold.collapsed_by_default,
                    })
                    .collect();
                let (items, count) = leak(items);
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnFoldingRanges {
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
pub unsafe extern "C" fn rln_folding_ranges_free(ranges: RlnFoldingRanges) {
    shallow((), || unsafe {
        reclaim(ranges.items, ranges.count);
        reclaim(ranges.strings, ranges.strings_length);
    });
}

/// The number of fold kinds, for checking a caller's table.
#[unsafe(no_mangle)]
pub extern "C" fn rln_fold_kind_count() -> u32 {
    FoldKind::Nonstructural as u32 + 1
}

/// The pair the delimiter beside `position` belongs to: the token on the
/// caret's right first, then the one on its left.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_brace_match(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    position: u32,
    out: *mut RlnBracePair,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (session, path, text) = match unsafe { arguments(session, path, text, out.is_null()) } {
            Ok(arguments) => arguments,
            Err(status) => return status,
        };
        match session.session.brace_match(path, position, text) {
            Ok(found) => {
                let pair = found.map_or_else(RlnBracePair::default, |pair| RlnBracePair {
                    open_start: pair.open_start,
                    open_end: pair.open_end,
                    close_start: pair.close_start,
                    close_end: pair.close_end,
                    found: true,
                });
                unsafe { out.write(pair) };
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

/// Hands a snippet, or its absence, to C.
unsafe fn answer_snippet(
    session: &RlnSession,
    found: Result<Option<Snippet>, rustlyn_ide::session::Refusal>,
    out: *mut RlnSnippet,
) -> RlnStatus {
    match found {
        Ok(snippet) => {
            let (changes, caret, found) = match snippet {
                Some(snippet) => (snippet.changes, snippet.caret, true),
                None => (Changes::default(), 0, false),
            };
            let mut edits = RlnEdits {
                items: std::ptr::null(),
                count: 0,
                renames: std::ptr::null(),
                rename_count: 0,
                strings: std::ptr::null(),
                strings_length: 0,
            };
            unsafe { write_edits(&raw mut edits, &changes) };
            unsafe {
                out.write(RlnSnippet {
                    edits,
                    caret,
                    found,
                });
            }
            RlnStatus::Ok
        }
        Err(refusal) => session.note(&refusal),
    }
}

/// What typing the third `/` of `///` expands into, with `position` the
/// caret after it. Free with `rln_snippet_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_doc_comment_on_typed(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    position: u32,
    out: *mut RlnSnippet,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        match unsafe { arguments(session, path, text, out.is_null()) } {
            Ok((session, path, text)) => unsafe {
                answer_snippet(
                    session,
                    session.session.doc_comment_on_typed(path, position, text),
                    out,
                )
            },
            Err(status) => status,
        }
    })
}

/// What Enter adds inside documentation, with `position` the start of the
/// new line and the line break already in the text. Free with
/// `rln_snippet_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_doc_comment_on_enter(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    position: u32,
    out: *mut RlnSnippet,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        match unsafe { arguments(session, path, text, out.is_null()) } {
            Ok((session, path, text)) => unsafe {
                answer_snippet(
                    session,
                    session.session.doc_comment_on_enter(path, position, text),
                    out,
                )
            },
            Err(status) => status,
        }
    })
}

/// The "insert comment" command: documentation above the declaration
/// around `position`. Free with `rln_snippet_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_insert_doc_comment(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    position: u32,
    out: *mut RlnSnippet,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        match unsafe { arguments(session, path, text, out.is_null()) } {
            Ok((session, path, text)) => unsafe {
                answer_snippet(
                    session,
                    session.session.insert_doc_comment(path, position, text),
                    out,
                )
            },
            Err(status) => status,
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_snippet_free(snippet: RlnSnippet) {
    shallow((), || unsafe {
        reclaim(snippet.edits.items, snippet.edits.count);
        reclaim(snippet.edits.renames, snippet.edits.rename_count);
        reclaim(snippet.edits.strings, snippet.edits.strings_length);
    });
}

/// Comments the lines of `start..end` with `//`, or uncomments them when
/// every one is. Free with `rln_edits_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_toggle_line_comment(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    start: u32,
    end: u32,
    out: *mut RlnEdits,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        match unsafe { arguments(session, path, text, out.is_null()) } {
            Ok((session, path, text)) => unsafe {
                answer_edits(
                    session,
                    session.session.toggle_line_comment(path, start, end, text),
                    out,
                )
            },
            Err(status) => status,
        }
    })
}

/// Wraps `start..end` in `/* */`, or unwraps the block comments it is.
/// Free with `rln_edits_free`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_toggle_block_comment(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    start: u32,
    end: u32,
    out: *mut RlnEdits,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        match unsafe { arguments(session, path, text, out.is_null()) } {
            Ok((session, path, text)) => unsafe {
                answer_edits(
                    session,
                    session.session.toggle_block_comment(path, start, end, text),
                    out,
                )
            },
            Err(status) => status,
        }
    })
}

// The layouts `rustlyn.h` promises, checked where they are declared.
const _: () = {
    assert!(size_of::<RlnFoldingRange>() == 28);
    assert!(size_of::<RlnBracePair>() == 20);
    assert!(size_of::<RlnSnippet>() == 6 * size_of::<usize>() + 8);
};

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;

    fn empty_edits() -> RlnEdits {
        RlnEdits {
            items: std::ptr::null(),
            count: 0,
            renames: std::ptr::null(),
            rename_count: 0,
            strings: std::ptr::null(),
            strings_length: 0,
        }
    }

    fn session() -> *mut RlnSession {
        let root = CString::new(std::env::temp_dir().to_string_lossy().as_bytes()).expect("a path");
        unsafe { crate::rln_session_new(root.as_ptr(), std::ptr::null(), std::ptr::null(), 0) }
    }

    #[test]
    fn format_fold_match_and_document_through_the_boundary() {
        let session = session();
        let path = CString::new("A.cs").expect("a path");
        let text =
            CString::new("class C {\nint x=1;\n  ///\n  void M(int a) { }\n}\n").expect("text");
        unsafe {
            let mut edits = empty_edits();
            assert_eq!(
                rln_format_document(session, path.as_ptr(), text.as_ptr(), &raw mut edits),
                RlnStatus::Ok
            );
            assert!(edits.count > 0);
            crate::rln_edits_free(edits);

            let mut ranges = RlnFoldingRanges {
                items: std::ptr::null(),
                count: 0,
                strings: std::ptr::null(),
                strings_length: 0,
            };
            assert_eq!(
                rln_block_structure(
                    session,
                    path.as_ptr(),
                    text.as_ptr(),
                    false,
                    &raw mut ranges
                ),
                RlnStatus::Ok
            );
            assert_eq!(ranges.count, 1);
            let first = *ranges.items;
            assert_eq!(first.kind, FoldKind::Type as u8);
            let banner = std::slice::from_raw_parts(ranges.strings, ranges.strings_length);
            assert_eq!(
                &banner[first.banner.offset as usize
                    ..(first.banner.offset + first.banner.length) as usize],
                b"..."
            );
            rln_folding_ranges_free(ranges);

            let mut pair = RlnBracePair::default();
            assert_eq!(
                rln_brace_match(session, path.as_ptr(), text.as_ptr(), 8, &raw mut pair),
                RlnStatus::Ok
            );
            assert!(pair.found);
            assert_eq!(pair.open_start, 8);

            let mut snippet = RlnSnippet {
                edits: empty_edits(),
                caret: 0,
                found: false,
            };
            let slashes = "class C {\nint x=1;\n  ///".len() as u32;
            assert_eq!(
                rln_doc_comment_on_typed(
                    session,
                    path.as_ptr(),
                    text.as_ptr(),
                    slashes,
                    &raw mut snippet
                ),
                RlnStatus::Ok
            );
            assert!(snippet.found);
            assert_eq!(snippet.edits.count, 1);
            rln_snippet_free(snippet);

            let mut indentation = RlnString {
                bytes: std::ptr::null(),
                length: 0,
            };
            assert_eq!(
                rln_indentation_for_new_line(
                    session,
                    path.as_ptr(),
                    text.as_ptr(),
                    9,
                    &raw mut indentation
                ),
                RlnStatus::Ok
            );
            // The file indents by two, so the new line does too.
            assert_eq!(
                std::slice::from_raw_parts(indentation.bytes, indentation.length),
                b"  "
            );
            crate::rln_text_free(indentation);

            let mut unused = empty_edits();
            assert_eq!(
                rln_format_on_type(
                    session,
                    path.as_ptr(),
                    text.as_ptr(),
                    0,
                    0xD800,
                    &raw mut unused
                ),
                RlnStatus::BadArgument
            );
            crate::rln_session_free(session);
        }
    }
}
