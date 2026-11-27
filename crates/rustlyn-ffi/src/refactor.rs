//! The refactorings Visual Studio drives through a dialog, across the
//! boundary: what each dialog lists, and each refactoring run with the
//! choices made in it.
//!
//! Every refactoring answers with an `RlnRefactorResult`: the edits, as any
//! `RlnEdits`, and why nothing changed when it could not be done — which is
//! `RLN_OK`, not a failure, since the dialog has something to show.

use std::ffi::c_char;
use std::path::Path;

use rustlyn_ide::semantic::{AddedParameter, ChangeParam, DialogKind, ExtractedMember};
use rustlyn_ide::session::RefactorResult;

use super::{
    RlnEdits, RlnSession, RlnStatus, RlnText, Strings, borrow, guard, held, leak, optional_text,
    pack_changes, reclaim, rln_edits_free, shallow,
};

/// One parameter of a changed signature: `existing` is the index of a
/// parameter there now, or negative for a new one described by the rest.
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct RlnChangeParam {
    pub existing: i32,
    pub type_name: *const c_char,
    pub name: *const c_char,
    /// Null for a required parameter.
    pub default_value: *const c_char,
    /// What existing calls pass; null to leave an optional one out.
    pub call_site: *const c_char,
}

/// A member chosen in a dialog, and whether it stays behind as an override
/// of a new abstract member.
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct RlnMemberChoice {
    pub name: *const c_char,
    pub make_abstract: u8,
}

/// A dialog's refactoring: its edits, or why there are none. `refused` is
/// in `edits.strings`. Freed with `rln_refactor_result_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnRefactorResult {
    pub edits: RlnEdits,
    pub refused: RlnText,
}

/// One parameter as the change-signature dialog lists it.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnSignatureParameter {
    /// `ref `, `out `, `in `, `this `, `params ` or empty.
    pub modifier: RlnText,
    pub type_name: RlnText,
    pub name: RlnText,
    pub default_value: RlnText,
    pub has_default: u8,
}

/// What the change-signature dialog shows. Freed with
/// `rln_signature_info_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnSignatureInfo {
    /// The member as one line.
    pub display: RlnText,
    /// Why the signature cannot change; empty when it can.
    pub refused: RlnText,
    pub parameters: *const RlnSignatureParameter,
    pub parameter_count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
    /// Whether the first parameter cannot move: an extension's `this`.
    pub first_is_fixed: u8,
}

/// One line of a dialog's member list.
#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub struct RlnDialogMember {
    /// What to hand back to choose it.
    pub name: RlnText,
    /// Its signature, as the list shows it.
    pub display: RlnText,
    pub selected: u8,
}

/// What a dialog lists. Freed with `rln_dialog_members_free`.
#[derive(Debug)]
#[repr(C)]
pub struct RlnDialogMembers {
    pub type_name: RlnText,
    /// The name suggested for the new type; empty when none is made.
    pub suggested_name: RlnText,
    /// Where the members can go, one per line: pull members up's base types.
    pub destinations: RlnText,
    /// Why there is nothing to list; empty otherwise.
    pub refused: RlnText,
    pub members: *const RlnDialogMember,
    pub member_count: usize,
    pub strings: *const u8,
    pub strings_length: usize,
}

/// `count` C strings, or `None` when one is null or not UTF-8.
unsafe fn strings_of(items: *const *const c_char, count: usize) -> Option<Vec<String>> {
    if count == 0 {
        return Some(Vec::new());
    }
    if items.is_null() {
        return None;
    }
    (0..count)
        .map(|index| unsafe { borrow(*items.add(index)) }.map(str::to_owned))
        .collect()
}

unsafe fn choices_of(items: *const RlnMemberChoice, count: usize) -> Option<Vec<ExtractedMember>> {
    if count == 0 {
        return Some(Vec::new());
    }
    if items.is_null() {
        return None;
    }
    (0..count)
        .map(|index| {
            let item = unsafe { *items.add(index) };
            Some(ExtractedMember {
                name: unsafe { borrow(item.name) }?.to_owned(),
                make_abstract: item.make_abstract != 0,
            })
        })
        .collect()
}

/// Hands a refactoring's answer to C.
unsafe fn write_result(out: *mut RlnRefactorResult, result: &RefactorResult) {
    let mut strings = Strings::default();
    let mut edits = Vec::new();
    let mut renames = Vec::new();
    pack_changes(&result.changes, &mut strings, &mut edits, &mut renames);
    let refused = strings.add(result.refused.as_deref().unwrap_or(""));
    let (items, count) = leak(edits);
    let (renames, rename_count) = leak(renames);
    let (bytes, strings_length) = leak(strings.bytes);
    unsafe {
        out.write(RlnRefactorResult {
            edits: RlnEdits {
                items,
                count,
                renames,
                rename_count,
                strings: bytes,
                strings_length,
            },
            refused,
        });
    }
}

/// The session, the path and the editor's text of a call, or `None` when
/// one of them is bad.
unsafe fn arguments<'a>(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
) -> Option<(&'a RlnSession, &'a str, Option<&'a str>)> {
    let session = unsafe { held(session) }?;
    let path = unsafe { borrow(path) }?;
    let text = unsafe { optional_text(text) }.ok()?;
    Some((session, path, text))
}

/// Runs a refactoring for C: bad arguments are `RLN_BAD_ARGUMENT`, a
/// refusal of the session is its status, and anything else an answer.
fn run(
    session: &RlnSession,
    out: *mut RlnRefactorResult,
    work: impl FnOnce() -> Result<RefactorResult, rustlyn_ide::session::Refusal>,
) -> RlnStatus {
    if out.is_null() {
        return RlnStatus::BadArgument;
    }
    match work() {
        Ok(result) => {
            unsafe { write_result(out, &result) };
            RlnStatus::Ok
        }
        Err(refusal) => session.note(&refusal),
    }
}

/// The method or constructor at `offset` (UTF-16) and its parameters. One
/// whose signature cannot change is `RLN_OK` with the reason in `refused`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_signature_info(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    out: *mut RlnSignatureInfo,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let Some((session, path, text)) = (unsafe { arguments(session, path, text) }) else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session
            .session
            .signature_info(Path::new(path), offset, text)
        {
            Ok(answer) => {
                let mut strings = Strings::default();
                let (display, refused, parameters, fixed) = match &answer {
                    Ok(target) => {
                        let display = strings.add(&target.display);
                        let parameters: Vec<RlnSignatureParameter> = target
                            .parameters
                            .iter()
                            .map(|parameter| RlnSignatureParameter {
                                modifier: strings.add(&parameter.modifier),
                                type_name: strings.add(&parameter.ty),
                                name: strings.add(&parameter.name),
                                default_value: strings
                                    .add(parameter.default.as_deref().unwrap_or("")),
                                has_default: u8::from(parameter.default.is_some()),
                            })
                            .collect();
                        (display, strings.add(""), parameters, target.first_is_fixed)
                    }
                    Err(why) => (strings.add(""), strings.add(why), Vec::new(), false),
                };
                let (parameters, parameter_count) = leak(parameters);
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnSignatureInfo {
                        display,
                        refused,
                        parameters,
                        parameter_count,
                        strings: bytes,
                        strings_length,
                        first_is_fixed: u8::from(fixed),
                    });
                }
                RlnStatus::Ok
            }
            Err(refusal) => session.note(&refusal),
        }
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_signature_info_free(info: RlnSignatureInfo) {
    shallow((), || unsafe {
        reclaim(info.parameters, info.parameter_count);
        reclaim(info.strings, info.strings_length);
    });
}

/// What the dialog of `kind` (`RLN_DIALOG_*`) lists for the type at
/// `offset`. Nothing to list is `RLN_OK` with the reason in `refused`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_dialog_members(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    kind: u32,
    out: *mut RlnDialogMembers,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some((session, path, text)), Some(kind)) = (
            unsafe { arguments(session, path, text) },
            DialogKind::from_u32(kind),
        ) else {
            return RlnStatus::BadArgument;
        };
        if out.is_null() {
            return RlnStatus::BadArgument;
        }
        match session
            .session
            .dialog_members(Path::new(path), offset, text, kind)
        {
            Ok(answer) => {
                let mut strings = Strings::default();
                let listed = answer.clone().unwrap_or_default();
                let type_name = strings.add(&listed.type_name);
                let suggested_name = strings.add(&listed.suggested_name);
                let destinations = strings.add_list(&listed.destinations);
                let refused = strings.add(answer.err().as_deref().unwrap_or(""));
                let members: Vec<RlnDialogMember> = listed
                    .members
                    .iter()
                    .map(|member| RlnDialogMember {
                        name: strings.add(&member.name),
                        display: strings.add(&member.display),
                        selected: u8::from(member.selected),
                    })
                    .collect();
                let (members, member_count) = leak(members);
                let (bytes, strings_length) = leak(strings.bytes);
                unsafe {
                    out.write(RlnDialogMembers {
                        type_name,
                        suggested_name,
                        destinations,
                        refused,
                        members,
                        member_count,
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
pub unsafe extern "C" fn rln_dialog_members_free(members: RlnDialogMembers) {
    shallow((), || unsafe {
        reclaim(members.members, members.member_count);
        reclaim(members.strings, members.strings_length);
    });
}

/// Changes the signature of the method or constructor at `offset` to the
/// `count` parameters of `params`, with every call across the project.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_change_signature(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    params: *const RlnChangeParam,
    count: usize,
    out: *mut RlnRefactorResult,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let Some((session, path, text)) = (unsafe { arguments(session, path, text) }) else {
            return RlnStatus::BadArgument;
        };
        if params.is_null() && count > 0 {
            return RlnStatus::BadArgument;
        }
        let mut order = Vec::with_capacity(count);
        for index in 0..count {
            let param = unsafe { *params.add(index) };
            if let Ok(existing) = usize::try_from(param.existing) {
                order.push(ChangeParam::Existing(existing));
                continue;
            }
            let (Some(ty), Some(name)) = (unsafe { borrow(param.type_name) }, unsafe {
                borrow(param.name)
            }) else {
                return RlnStatus::BadArgument;
            };
            order.push(ChangeParam::Added(AddedParameter {
                ty: ty.to_owned(),
                name: name.to_owned(),
                default: unsafe { borrow(param.default_value) }.map(str::to_owned),
                call_site: unsafe { borrow(param.call_site) }.map(str::to_owned),
            }));
        }
        run(session, out, || {
            session
                .session
                .change_signature(Path::new(path), offset, text, &order)
        })
    })
}

/// Extracts an interface called `name` declaring the `count` members named
/// in `members` from the type at `offset`, in a new file when `new_file`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_extract_interface(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    name: *const c_char,
    members: *const *const c_char,
    count: usize,
    new_file: u8,
    out: *mut RlnRefactorResult,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some((session, path, text)), Some(name), Some(members)) = (
            unsafe { arguments(session, path, text) },
            unsafe { borrow(name) },
            unsafe { strings_of(members, count) },
        ) else {
            return RlnStatus::BadArgument;
        };
        run(session, out, || {
            session.session.extract_interface(
                Path::new(path),
                offset,
                text,
                name,
                &members,
                new_file != 0,
            )
        })
    })
}

/// Extracts a base class called `name` from the class at `offset`, moving
/// the `count` members of `members` or leaving them as overrides.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_extract_base_class(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    name: *const c_char,
    members: *const RlnMemberChoice,
    count: usize,
    new_file: u8,
    out: *mut RlnRefactorResult,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some((session, path, text)), Some(name), Some(members)) = (
            unsafe { arguments(session, path, text) },
            unsafe { borrow(name) },
            unsafe { choices_of(members, count) },
        ) else {
            return RlnStatus::BadArgument;
        };
        run(session, out, || {
            session.session.extract_base_class(
                Path::new(path),
                offset,
                text,
                name,
                &members,
                new_file != 0,
            )
        })
    })
}

/// Pulls the `count` members of `members` of the type at `offset` up to
/// its base type called `destination`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_pull_members_up(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    destination: *const c_char,
    members: *const RlnMemberChoice,
    count: usize,
    out: *mut RlnRefactorResult,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some((session, path, text)), Some(destination), Some(members)) = (
            unsafe { arguments(session, path, text) },
            unsafe { borrow(destination) },
            unsafe { choices_of(members, count) },
        ) else {
            return RlnStatus::BadArgument;
        };
        run(session, out, || {
            session
                .session
                .pull_members_up(Path::new(path), offset, text, destination, &members)
        })
    })
}

/// Overrides the `count` inherited members of `members` (as
/// `rln_dialog_members` lists them, or by name) in the type at `offset`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_generate_overrides(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    members: *const *const c_char,
    count: usize,
    out: *mut RlnRefactorResult,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some((session, path, text)), Some(members)) =
            (unsafe { arguments(session, path, text) }, unsafe {
                strings_of(members, count)
            })
        else {
            return RlnStatus::BadArgument;
        };
        run(session, out, || {
            session
                .session
                .generate_overrides(Path::new(path), offset, text, &members)
        })
    })
}

/// Moves the `count` static members of `members` of the type at `offset`
/// to the type called `destination`, made (in a new file when `new_file`)
/// when the project has none.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_move_static_members(
    session: *mut RlnSession,
    path: *const c_char,
    text: *const c_char,
    offset: u32,
    destination: *const c_char,
    members: *const *const c_char,
    count: usize,
    new_file: u8,
    out: *mut RlnRefactorResult,
) -> RlnStatus {
    guard(RlnStatus::Panicked, || {
        let (Some((session, path, text)), Some(destination), Some(members)) = (
            unsafe { arguments(session, path, text) },
            unsafe { borrow(destination) },
            unsafe { strings_of(members, count) },
        ) else {
            return RlnStatus::BadArgument;
        };
        run(session, out, || {
            session.session.move_static_members(
                Path::new(path),
                offset,
                text,
                destination,
                &members,
                new_file != 0,
            )
        })
    })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rln_refactor_result_free(result: RlnRefactorResult) {
    shallow((), || unsafe { rln_edits_free(result.edits) });
}

/// The layout the header promises for the refactoring dialogs.
const _: () = {
    assert!(size_of::<RlnChangeParam>() == 40);
    assert!(size_of::<RlnMemberChoice>() == 16);
    assert!(size_of::<RlnRefactorResult>() == 56);
    assert!(size_of::<RlnSignatureParameter>() == 36);
    assert!(size_of::<RlnSignatureInfo>() == 56);
    assert!(size_of::<RlnDialogMember>() == 20);
    assert!(size_of::<RlnDialogMembers>() == 64);
    assert!(DialogKind::MoveStaticMembers as u8 == 4);
};
