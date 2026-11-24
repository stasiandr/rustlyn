//! Walking a method body and checking that the stack adds up.
//!
//! A runtime refuses a body whose stack does not balance with
//! `InvalidProgramException` and nothing else: no offset, no instruction, no
//! reason. That is the least it could say and the most it will, so a compiler
//! that writes IL needs its own answer to the same question. This gives one.
//!
//! Only the *depth* is tracked, not what is on the stack. That is enough to
//! catch what a code generator gets wrong — a branch that arrives with a value
//! nobody left, a call whose arity was counted from the wrong signature, a
//! `maxstack` that is too small — and it needs nothing but the body, the
//! opcode table and the signature of whatever each call names.

use std::collections::HashMap;

use crate::body::{Body, Handler, Value};
use crate::reader::Assembly;
use crate::signature::{Blob, TypeSig};
use crate::{Token, table, tables};

/// Something about a body that a runtime would refuse.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Complaint {
    /// Where in the body, as the offset a disassembly prints.
    pub offset: u32,
    pub message: String,
}

/// Checks one body's stack, returning everything wrong with it.
///
/// An empty answer means the depth balances everywhere and stays inside
/// `maxstack`. It does not mean the body is correct — nothing here looks at
/// what the values *are*.
#[must_use]
pub fn stack(assembly: &Assembly<'_>, body: &Body) -> Vec<Complaint> {
    let mut complaints = Vec::new();
    let index: HashMap<u32, usize> = body
        .instructions
        .iter()
        .enumerate()
        .map(|(at, instruction)| (instruction.offset, at))
        .collect();

    // Everywhere control can start: the first instruction, and every handler,
    // which the runtime enters with what it put there — one value for a catch
    // or a filter, nothing for a finally.
    let mut queue: Vec<(u32, i32)> = vec![(0, 0)];
    for region in &body.regions {
        queue.push((region.try_offset, 0));
        queue.push((
            region.handler_offset,
            match region.kind {
                Handler::Finally | Handler::Fault => 0,
                Handler::Catch(_) | Handler::Filter(_) => 1,
            },
        ));
        if let Handler::Filter(offset) = region.kind {
            queue.push((offset, 1));
        }
    }

    let mut depths: HashMap<u32, i32> = HashMap::new();
    while let Some((from, mut depth)) = queue.pop() {
        let Some(mut at) = index.get(&from).copied() else {
            continue;
        };
        loop {
            let instruction = &body.instructions[at];
            match depths.get(&instruction.offset) {
                // Already walked from here, and with the same answer.
                Some(known) if *known == depth => break,
                Some(known) => {
                    complaints.push(Complaint {
                        offset: instruction.offset,
                        message: format!("reached with {depth} on the stack and with {known}"),
                    });
                    break;
                }
                None => {
                    depths.insert(instruction.offset, depth);
                }
            }

            // §III.3.56: `ret` may not carry control out of a protected
            // region. Leaving one is what `leave` is for, and a runtime
            // meeting a `ret` inside one refuses the body.
            if instruction.opcode == 0x2A
                && body
                    .regions
                    .iter()
                    .any(|region| encloses(region, instruction.offset))
            {
                complaints.push(Complaint {
                    offset: instruction.offset,
                    message: "`ret` inside a protected region, which has to be left".to_string(),
                });
            }
            // `constrained.` says the receiver is an address of whatever
            // follows, which is exactly how a value type's virtual method is
            // reached: the `callvirt` after one is not a dispatch on a value.
            let constrained = at > 0 && body.instructions[at - 1].opcode == 0xFE16;
            if let Some(message) = (!constrained)
                .then(|| misuse(assembly, instruction.opcode, &instruction.value))
                .flatten()
            {
                complaints.push(Complaint {
                    offset: instruction.offset,
                    message,
                });
            }
            let (pops, pushes) = effect(assembly, instruction.opcode, &instruction.value);
            if depth < pops {
                complaints.push(Complaint {
                    offset: instruction.offset,
                    message: format!(
                        "`{}` takes {pops} from a stack holding {depth}",
                        instruction.name
                    ),
                });
                depth = pops;
            }
            depth = depth - pops + pushes;
            if depth > i32::from(body.max_stack) {
                complaints.push(Complaint {
                    offset: instruction.offset,
                    message: format!(
                        "the stack reaches {depth}, past the {} the header promises",
                        body.max_stack
                    ),
                });
            }

            // `leave` empties the stack on its way out of a protected region.
            let arriving = if matches!(instruction.opcode, 0xDD | 0xDE) {
                0
            } else {
                depth
            };
            for target in targets(&instruction.value) {
                queue.push((target, arriving));
            }
            if ends_flow(instruction.opcode) {
                break;
            }
            at += 1;
            if at >= body.instructions.len() {
                break;
            }
        }
    }
    complaints
}

/// An instruction used on something it cannot be used on.
///
/// A value type has no vtable to dispatch through and no reference to load:
/// `callvirt` on one is not a program, and a runtime meeting one may refuse
/// the body or fall over trying to compile it.
fn misuse(assembly: &Assembly<'_>, opcode: u16, value: &Value) -> Option<String> {
    if opcode != 0x6F {
        return None;
    }
    let Value::Token(token) = value else {
        return None;
    };
    let (name, declaring) = declaring_type(assembly, *token)?;
    is_value_type(assembly, declaring)
        .then(|| format!("`callvirt {name}` dispatches on a value type"))
}

/// The name of a member's declaring type and the token naming it.
fn declaring_type(assembly: &Assembly<'_>, token: Token) -> Option<(String, Token)> {
    let heaps = assembly.heaps();
    match token.table() {
        table::MEMBER_REF => {
            let row = assembly.row(token)?;
            let (number, at) = tables::MEMBER_REF_PARENT.decode(row.number(0))?;
            Some((
                heaps.string(row.number(1)).to_string(),
                Token::new(number, at),
            ))
        }
        table::METHOD_SPEC => {
            let row = assembly.row(token)?;
            let (number, at) = tables::METHOD_DEF_OR_REF.decode(row.number(0))?;
            declaring_type(assembly, Token::new(number, at))
        }
        // A `MethodDef` belongs to whichever type's run of methods holds it,
        // which is a search rather than a column.
        table::METHOD_DEF => {
            let types = assembly.table(table::TYPE_DEF);
            let owner = types
                .iter()
                .enumerate()
                .filter(|(_, ty)| ty.number(5) <= token.row())
                .map(|(at, _)| at as u32 + 1)
                .last()?;
            let row = assembly.row(token)?;
            Some((
                heaps.string(row.number(3)).to_string(),
                Token::new(table::TYPE_DEF, owner),
            ))
        }
        _ => None,
    }
}

/// Whether a type is a value type, following a `TypeSpec` into its signature.
fn is_value_type(assembly: &Assembly<'_>, token: Token) -> bool {
    match token.table() {
        // The signature says so in its own first byte.
        table::TYPE_SPEC => assembly
            .row(token)
            .and_then(|row| assembly.heaps().blob(row.number(0)).ok())
            .and_then(|bytes| Blob::new(bytes).type_sig().ok())
            .is_some_and(|ty| {
                matches!(
                    ty,
                    crate::signature::TypeSig::ValueType(_)
                        | crate::signature::TypeSig::Generic { .. }
                ) && !matches!(ty, crate::signature::TypeSig::Generic { ref definition, .. }
                    if matches!(**definition, crate::signature::TypeSig::Class(_)))
            }),
        // A `TypeDef` says so by what it extends.
        table::TYPE_DEF => assembly
            .row(token)
            .and_then(|row| tables::TYPE_DEF_OR_REF.decode(row.number(3)))
            .and_then(|(number, at)| {
                let row = assembly.table(number).row(at)?;
                let heaps = assembly.heaps();
                Some(matches!(
                    (heaps.string(row.number(2)), heaps.string(row.number(1))),
                    ("System", "ValueType" | "Enum")
                ))
            })
            .unwrap_or(false),
        _ => false,
    }
}

/// Whether an offset falls inside one of a region's three parts.
fn encloses(region: &crate::body::Region, offset: u32) -> bool {
    let inside = |start: u32, length: u32| offset >= start && offset < start + length;
    inside(region.try_offset, region.try_length)
        || inside(region.handler_offset, region.handler_length)
}

/// Whether nothing after this instruction is reached from it.
const fn ends_flow(opcode: u16) -> bool {
    matches!(
        opcode,
        // ret, jmp, throw, rethrow, endfinally, endfilter, br, br.s,
        // leave, leave.s
        0x2A | 0x27 | 0x7A | 0xFE1A | 0xDC | 0xFE11 | 0x38 | 0x2B | 0xDD | 0xDE
    )
}

/// The offsets an instruction can branch to, the next one aside.
fn targets(value: &Value) -> Vec<u32> {
    match value {
        Value::Target(target) => vec![*target],
        Value::Targets(cases) => cases.clone(),
        _ => Vec::new(),
    }
}

/// How many values an instruction takes and leaves.
fn effect(assembly: &Assembly<'_>, opcode: u16, value: &Value) -> (i32, i32) {
    match opcode {
        // Calls are the only ones whose arity is not in the opcode.
        0x28 | 0x6F => call_effect(assembly, value, false),
        0x73 => call_effect(assembly, value, true),
        0x29 => (1, 1),
        _ => fixed(opcode),
    }
}

/// What a `call`, `callvirt` or `newobj` does to the stack, from the signature
/// of whatever it names.
fn call_effect(assembly: &Assembly<'_>, value: &Value, creating: bool) -> (i32, i32) {
    let Value::Token(token) = value else {
        return (0, 0);
    };
    let Some((instance, parameters, returns)) = signature_of(assembly, *token) else {
        return (0, 0);
    };
    if creating {
        // `newobj` runs a constructor and leaves what it made; it is handed no
        // `this`, because that is what it is producing.
        return (parameters, 1);
    }
    (parameters + i32::from(instance), i32::from(returns))
}

/// Whether a member takes a `this`, how many parameters it has, and whether it
/// gives anything back.
fn signature_of(assembly: &Assembly<'_>, token: Token) -> Option<(bool, i32, bool)> {
    let heaps = assembly.heaps();
    let row = assembly.row(token)?;
    let blob = match token.table() {
        table::METHOD_DEF => row.number(4),
        table::MEMBER_REF => row.number(2),
        table::METHOD_SPEC => {
            // A constructed method: the shape is the definition's.
            let (number, at) = tables::METHOD_DEF_OR_REF.decode(row.number(0))?;
            return signature_of(assembly, Token::new(number, at));
        }
        _ => return None,
    };
    let bytes = heaps.blob(blob).ok()?;
    let sig = Blob::new(bytes).method_sig().ok()?;
    Some((
        sig.instance,
        sig.parameters.len() as i32,
        !matches!(sig.returns, crate::signature::TypeSig::Void),
    ))
}

/// What every other opcode does to the stack.
#[allow(clippy::match_same_arms)]
const fn fixed(opcode: u16) -> (i32, i32) {
    match opcode {
        // nop, break, and every prefix
        0x00 | 0x01 | 0xFE12..=0xFE14 | 0xFE16 | 0xFE19 | 0xFE1E => (0, 0),
        // ldarg.0..3, ldloc.0..3, ldarg.s, ldarga.s, ldloc.s, ldloca.s
        0x02..=0x09 | 0x0E | 0x0F | 0x11 | 0x12 => (0, 1),
        // starg.s, stloc.s, stloc.0..3
        0x0A..=0x0D | 0x10 | 0x13 => (1, 0),
        // ldnull, ldc.*
        0x14..=0x23 => (0, 1),
        0x25 => (1, 2),                      // dup
        0x26 => (1, 0),                      // pop
        0x27 => (0, 0),                      // jmp
        0x2A => (0, 0),                      // ret: what it takes is the return type's business
        0x2B | 0x38 => (0, 0),               // br
        0x2C | 0x2D | 0x39 | 0x3A => (1, 0), // brfalse, brtrue
        0x2E..=0x37 | 0x3B..=0x44 => (2, 0), // the comparing branches
        0x45 => (1, 0),                      // switch
        0x46..=0x50 => (1, 1),               // ldind.*
        0x51..=0x57 => (2, 0),               // stind.*
        0x58..=0x64 => (2, 1),               // add through shr.un
        0x65 | 0x66 => (1, 1),               // neg, not
        0x67..=0x6E => (1, 1),               // conversions
        0x70 => (2, 0),                      // cpobj
        0x71 => (1, 1),                      // ldobj
        0x72 => (0, 1),                      // ldstr
        0x74 | 0x75 => (1, 1),               // castclass, isinst
        0x76 => (1, 1),                      // conv.r.un
        0x79 => (1, 1),                      // unbox
        0x7A => (1, 0),                      // throw
        0x7B | 0x7C => (1, 1),               // ldfld, ldflda
        0x7D => (2, 0),                      // stfld
        0x7E | 0x7F => (0, 1),               // ldsfld, ldsflda
        0x80 => (1, 0),                      // stsfld
        0x81 => (2, 0),                      // stobj
        0x82..=0x8C => (1, 1),               // the checked conversions and box
        0x8D => (1, 1),                      // newarr
        0x8E => (1, 1),                      // ldlen
        0x8F => (2, 1),                      // ldelema
        0x90..=0x9A | 0xA3 => (2, 1),        // ldelem.*
        0x9B..=0xA2 | 0xA4 => (3, 0),        // stelem.*
        0xA5 => (1, 1),                      // unbox.any
        0xB3..=0xBA => (1, 1),               // more checked conversions
        0xC2 => (1, 1),                      // refanyval
        0xC3 => (1, 1),                      // ckfinite
        0xC6 => (1, 1),                      // mkrefany
        0xD0 => (0, 1),                      // ldtoken
        0xD1..=0xD5 | 0xE0 => (1, 1),        // conv.*
        0xD6..=0xDB => (2, 1),               // the overflow-checked arithmetic
        0xDC => (0, 0),                      // endfinally
        0xDD | 0xDE => (0, 0),               // leave empties the stack, handled by the caller
        0xDF => (2, 0),                      // stind.i
        0xFE00 => (0, 1),                    // arglist
        0xFE01..=0xFE05 => (2, 1),           // ceq and the comparisons
        0xFE06 => (0, 1),                    // ldftn
        0xFE07 => (1, 1),                    // ldvirtftn
        0xFE09 | 0xFE0A | 0xFE0C | 0xFE0D => (0, 1),
        0xFE0B | 0xFE0E => (1, 0),
        0xFE0F => (1, 1),          // localloc
        0xFE11 => (1, 0),          // endfilter
        0xFE15 => (1, 0),          // initobj
        0xFE17 | 0xFE18 => (3, 0), // cpblk, initblk
        0xFE1A => (0, 0),          // rethrow
        0xFE1C => (0, 1),          // sizeof
        0xFE1D => (1, 1),          // refanytype
        _ => (0, 0),
    }
}

/// Checks that no instruction names a member of a generic type by the
/// member's own definition.
///
/// A generic type has no members until it is constructed: `Box`1::Get` is a
/// definition and `Box<int>::Get` is the method, and only the second can be
/// called. An instruction that names the first loads but is refused the
/// moment the runtime looks at it — as `BadImageFormatException`, which says
/// nothing about where. This says where, for every body at once.
#[must_use]
pub fn definitions(assembly: &Assembly<'_>, body: &Body, owner: u32) -> Vec<Complaint> {
    let generic = generic_types(assembly);
    let mut complaints = Vec::new();
    for instruction in &body.instructions {
        let Value::Token(token) = instruction.value else {
            continue;
        };
        let Some(declaring) = declaring_row(assembly, token) else {
            continue;
        };
        if !generic.contains(&declaring) {
            continue;
        }
        // A body of the type itself may still not name it bare, but saying so
        // for every member of every generic type would drown the ones that
        // matter; what the runtime refuses outright is naming another type's.
        if declaring == owner {
            continue;
        }
        complaints.push(Complaint {
            offset: instruction.offset,
            message: format!(
                "`{}` names a member of the generic type in row {declaring} by its definition, \
                 which is not a member until the type is constructed",
                instruction.name
            ),
        });
    }
    complaints
}

/// Every `TypeDef` row that declares type parameters of its own.
fn generic_types(assembly: &Assembly<'_>) -> std::collections::HashSet<u32> {
    let mut found = std::collections::HashSet::new();
    for row in assembly.table(table::GENERIC_PARAM).iter() {
        let owner = row.token(2);
        if owner.table() == table::TYPE_DEF {
            found.insert(owner.row());
        }
    }
    found
}

/// The `TypeDef` row a `MethodDef` or `Field` token belongs to.
fn declaring_row(assembly: &Assembly<'_>, token: Token) -> Option<u32> {
    let column = match token.table() {
        table::METHOD_DEF => 5,
        table::FIELD => 4,
        _ => return None,
    };
    let types = assembly.table(table::TYPE_DEF);
    let mut owner = None;
    for (index, ty) in types.iter().enumerate() {
        if ty.number(column) <= token.row() {
            owner = Some(index as u32 + 1);
        } else {
            break;
        }
    }
    owner
}

/// Every construction in the assembly whose argument count does not match the
/// number of parameters it constructs.
///
/// `Holder`2<int>` is not a type: the runtime refuses the signature the moment
/// it reads it, and says only `BadImageFormatException` with no offset and no
/// name. There is no way to find the one wrong blob among thirty thousand by
/// running it, so this reads them all.
///
/// Only a construction of a type or method *this* assembly defines is checked;
/// a referenced one's arity is in the other assembly, which is not here.
#[must_use]
pub fn arities(assembly: &Assembly<'_>) -> Vec<String> {
    let heaps = assembly.heaps();
    let mut type_arity: HashMap<u32, usize> = HashMap::new();
    let mut method_arity: HashMap<u32, usize> = HashMap::new();
    for row in assembly.table(table::GENERIC_PARAM).iter() {
        let owner = row.number(2);
        let (tag, index) = (owner & 0x0001, owner >> 1);
        let counts = if tag == 0 {
            &mut type_arity
        } else {
            &mut method_arity
        };
        *counts.entry(index).or_default() += 1;
    }

    let mut complaints = Vec::new();
    let mut check = |where_at: &str, bytes: &[u8], read: fn(&mut Blob<'_>) -> Vec<TypeSig>| {
        for ty in read(&mut Blob::new(bytes)) {
            walk(&ty, &type_arity, where_at, &mut complaints);
        }
    };
    for (at, row) in assembly.table(table::TYPE_SPEC).iter().enumerate() {
        let Ok(bytes) = heaps.blob(row.number(0)) else {
            continue;
        };
        check(&format!("TypeSpec {}", at + 1), bytes, |blob| {
            blob.type_sig().into_iter().collect()
        });
    }
    for (at, row) in assembly.table(table::FIELD).iter().enumerate() {
        let Ok(bytes) = heaps.blob(row.number(2)) else {
            continue;
        };
        check(&format!("Field {}", at + 1), bytes, |blob| {
            blob.field_sig().into_iter().collect()
        });
    }
    for (at, row) in assembly.table(table::STAND_ALONE_SIG).iter().enumerate() {
        let Ok(bytes) = heaps.blob(row.number(0)) else {
            continue;
        };
        check(&format!("StandAloneSig {}", at + 1), bytes, |blob| {
            blob.locals_sig().unwrap_or_default()
        });
    }
    for (table, column, name) in [
        (table::METHOD_DEF, 4, "MethodDef"),
        (table::MEMBER_REF, 2, "MemberRef"),
        (table::PROPERTY, 2, "Property"),
    ] {
        for (at, row) in assembly.table(table).iter().enumerate() {
            let Ok(bytes) = heaps.blob(row.number(column)) else {
                continue;
            };
            let mut blob = Blob::new(bytes);
            let signature = if table == table::PROPERTY {
                blob.property_sig()
            } else {
                blob.method_sig()
            };
            let Ok(signature) = signature else {
                continue;
            };
            let where_at = format!("{name} {}", at + 1);
            walk(&signature.returns, &type_arity, &where_at, &mut complaints);
            for parameter in &signature.parameters {
                walk(parameter, &type_arity, &where_at, &mut complaints);
            }
        }
    }

    // A `MethodSpec` says which method and what it was given, and those two
    // numbers have to agree just as a type's do.
    for (at, row) in assembly.table(table::METHOD_SPEC).iter().enumerate() {
        let Ok(bytes) = heaps.blob(row.number(1)) else {
            continue;
        };
        let mut blob = Blob::new(bytes);
        // §II.23.2.15: `GENERICINST` then the count, then the arguments.
        if blob.byte() != Ok(0x0A) {
            continue;
        }
        let Ok(count) = blob.unsigned() else {
            continue;
        };
        let mut arguments = Vec::new();
        for _ in 0..count {
            match blob.type_sig() {
                Ok(argument) => arguments.push(argument),
                Err(_) => break,
            }
        }
        let where_at = format!("MethodSpec {}", at + 1);
        for argument in &arguments {
            walk(argument, &type_arity, &where_at, &mut complaints);
        }
        let parent = row.number(0);
        if parent & 0x0001 != 0 {
            continue;
        }
        let declared = method_arity.get(&(parent >> 1)).copied().unwrap_or(0);
        if declared != count as usize {
            complaints.push(format!(
                "{where_at}: MethodDef {} takes {declared} type arguments and was given {count}",
                parent >> 1
            ));
        }
    }
    complaints
}

/// Walks a signature, complaining about every construction that gives a type
/// this assembly defines the wrong number of arguments.
fn walk(ty: &TypeSig, arity: &HashMap<u32, usize>, where_at: &str, into: &mut Vec<String>) {
    match ty {
        TypeSig::Generic {
            definition,
            arguments,
        } => {
            if let TypeSig::Class(token) | TypeSig::ValueType(token) = definition.as_ref()
                && token.0 >> 24 == u32::from(table::TYPE_DEF)
            {
                let row = token.0 & 0x00FF_FFFF;
                let declared = arity.get(&row).copied().unwrap_or(0);
                if declared != arguments.len() {
                    into.push(format!(
                        "{where_at}: TypeDef {row} takes {declared} type arguments and was given {}",
                        arguments.len()
                    ));
                }
            }
            walk(definition, arity, where_at, into);
            for argument in arguments {
                walk(argument, arity, where_at, into);
            }
        }
        TypeSig::Vector(inner)
        | TypeSig::Array { element: inner, .. }
        | TypeSig::Pointer(inner)
        | TypeSig::ByRef(inner) => walk(inner, arity, where_at, into),
        _ => {}
    }
}

/// Every token in a body that names a type parameter the body has no view of.
///
/// `<>c__DisplayClass<!!0>` written in a method of that class means the first
/// parameter of *that method*, and a method with none has no `!!0` to give:
/// the runtime reads the signature, finds nothing there, and says
/// `BadImageFormatException` with no offset and no token. The same goes for
/// `!0` past the end of the type's own parameters.
#[must_use]
pub fn scopes(
    assembly: &Assembly<'_>,
    body: &Body,
    type_parameters: usize,
    method_parameters: usize,
) -> Vec<Complaint> {
    let heaps = assembly.heaps();
    let mut complaints = Vec::new();
    let blame = |offset: u32, name: &str, ty: &TypeSig, complaints: &mut Vec<Complaint>| {
        let mut over = Vec::new();
        beyond(ty, type_parameters, method_parameters, &mut over);
        for message in over {
            complaints.push(Complaint {
                offset,
                message: format!("`{name}` names {message}"),
            });
        }
    };
    for instruction in &body.instructions {
        let Value::Token(token) = instruction.value else {
            continue;
        };
        // What the token hangs off: a `TypeSpec` itself, the parent of a
        // `MemberRef`, or what a `MethodSpec` constructs.
        let mut blobs: Vec<u32> = Vec::new();
        match token.table() {
            table::TYPE_SPEC => {
                if let Some(row) = assembly.table(table::TYPE_SPEC).row(token.row()) {
                    blobs.push(row.number(0));
                }
            }
            table::MEMBER_REF => {
                if let Some(row) = assembly.table(table::MEMBER_REF).row(token.row()) {
                    let parent = row.number(0);
                    // A `MemberRefParent` tagged 4 is a `TypeSpec`.
                    if parent & 0x0007 == 4
                        && let Some(spec) = assembly.table(table::TYPE_SPEC).row(parent >> 3)
                    {
                        blobs.push(spec.number(0));
                    }
                }
            }
            table::METHOD_SPEC => {
                if let Some(row) = assembly.table(table::METHOD_SPEC).row(token.row()) {
                    blobs.push(row.number(1));
                    let parent = row.number(0);
                    // A `MethodDefOrRef` tagged 1 is a `MemberRef`.
                    if parent & 0x0001 == 1
                        && let Some(member) = assembly.table(table::MEMBER_REF).row(parent >> 1)
                        && member.number(0) & 0x0007 == 4
                        && let Some(spec) =
                            assembly.table(table::TYPE_SPEC).row(member.number(0) >> 3)
                    {
                        blobs.push(spec.number(0));
                    }
                }
            }
            _ => continue,
        }
        for blob in blobs {
            let Ok(bytes) = heaps.blob(blob) else {
                continue;
            };
            let mut reader = Blob::new(bytes);
            // A `MethodSpec` blob is `GENERICINST` then a count; a `TypeSpec`
            // is one type. Reading types until the blob runs out covers both.
            if bytes.first() == Some(&0x0A) {
                let _ = reader.byte();
                let _ = reader.unsigned();
            }
            while !reader.is_done() {
                let Ok(ty) = reader.type_sig() else {
                    break;
                };
                blame(instruction.offset, instruction.name, &ty, &mut complaints);
            }
        }
    }
    complaints
}

/// Collects every type parameter a signature names past what is in scope.
fn beyond(ty: &TypeSig, type_parameters: usize, method_parameters: usize, into: &mut Vec<String>) {
    match ty {
        TypeSig::Var(index) if *index as usize >= type_parameters => {
            into.push(format!(
                "`!{index}` where the type declares {type_parameters}"
            ));
        }
        TypeSig::MVar(index) if *index as usize >= method_parameters => {
            into.push(format!(
                "`!!{index}` where the method declares {method_parameters}"
            ));
        }
        TypeSig::Generic {
            definition,
            arguments,
        } => {
            beyond(definition, type_parameters, method_parameters, into);
            for argument in arguments {
                beyond(argument, type_parameters, method_parameters, into);
            }
        }
        TypeSig::Vector(inner)
        | TypeSig::Array { element: inner, .. }
        | TypeSig::Pointer(inner)
        | TypeSig::ByRef(inner) => beyond(inner, type_parameters, method_parameters, into),
        _ => {}
    }
}
