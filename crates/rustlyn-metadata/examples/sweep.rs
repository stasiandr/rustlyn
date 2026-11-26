//! Decodes every method body in an assembly and says what did not decode.
//!
//! ```sh
//! cargo run --release -p rustlyn-metadata --example sweep -- System.Private.CoreLib.dll
//! ```
//!
//! This is the check that matters for the opcode table. Reading IL is a walk
//! with no landmarks: an opcode whose operand width is wrong does not skip an
//! instruction, it lands in the middle of one, and what comes out after that
//! is nonsense that still decodes. On a large enough assembly a wrong width
//! runs into something that does not decode at all, which is what this looks
//! for.

use rustlyn_metadata::{Assembly, Body, TypeSig, table};

fn main() {
    let mut bodies = 0u32;
    let mut abstract_or_runtime = 0u32;
    let mut instructions = 0u64;
    let mut signatures = 0u64;
    let mut unknown = std::collections::BTreeMap::<u8, u32>::new();
    let mut failed = Vec::new();

    for path in std::env::args().skip(1) {
        let Ok(bytes) = std::fs::read(&path) else {
            eprintln!("{path}: cannot be read");
            continue;
        };
        let assembly = match Assembly::read(&bytes) {
            Ok(assembly) => assembly,
            Err(error) => {
                eprintln!("{path}: {error}");
                continue;
            }
        };
        let heaps = assembly.heaps();

        // Every signature in the assembly, read back. A blob that does not
        // parse says so; one that parses into `Unknown` says which element
        // type this reader does not model, which is the more useful answer.
        {
            let mut signature = |blob: u32, what: &str, kind: SigKind| {
                let Ok(bytes) = heaps.blob(blob) else {
                    failed.push(format!("{path}: {what}: the blob is out of range"));
                    return;
                };
                let mut reader = rustlyn_metadata::Blob::new(bytes);
                let read = match kind {
                    SigKind::Method => reader.method_sig().map(|sig| {
                        let mut all = sig.parameters;
                        all.push(sig.returns);
                        all
                    }),
                    SigKind::Field => reader.field_sig().map(|ty| vec![ty]),
                    SigKind::Property => reader.property_sig().map(|sig| {
                        let mut all = sig.parameters;
                        all.push(sig.returns);
                        all
                    }),
                    SigKind::Locals => reader.locals_sig(),
                    SigKind::Type => reader.type_sig().map(|ty| vec![ty]),
                };
                match read {
                    Ok(types) => {
                        signatures += 1;
                        for ty in &types {
                            count_unknown(ty, &mut unknown);
                        }
                    }
                    Err(error) => failed.push(format!("{path}: {what}: {error}")),
                }
            };
            for row in assembly.table(table::FIELD).iter() {
                signature(row.number(2), "a field", SigKind::Field);
            }
            for row in assembly.table(table::PROPERTY).iter() {
                signature(row.number(2), "a property", SigKind::Property);
            }
            for row in assembly.table(table::STAND_ALONE_SIG).iter() {
                signature(row.number(0), "a locals list", SigKind::Locals);
            }
            for row in assembly.table(table::TYPE_SPEC).iter() {
                signature(row.number(0), "a constructed type", SigKind::Type);
            }
            for row in assembly.table(table::METHOD_DEF).iter() {
                signature(row.number(4), "a method", SigKind::Method);
            }
            for row in assembly.table(table::MEMBER_REF).iter() {
                // A `MemberRef` is a method or a field, and the convention says
                // which: `FIELD` is 0x06.
                let kind = match heaps.blob(row.number(2)).ok().and_then(|b| b.first()) {
                    Some(0x06) => SigKind::Field,
                    _ => SigKind::Method,
                };
                signature(row.number(2), "a referenced member", kind);
            }
        }

        for method in assembly.table(table::METHOD_DEF).iter() {
            let rva = method.number(0);
            if rva == 0 {
                abstract_or_runtime += 1;
                continue;
            }
            let name = heaps.string(method.number(3));
            let Ok(rest) = assembly.image().from_rva(rva) else {
                failed.push(format!("{path}: {name}: address {rva:#x} is in no section"));
                continue;
            };
            match Body::read(rest) {
                Ok(body) => {
                    bodies += 1;
                    instructions += body.instructions.len() as u64;
                }
                Err(error) => failed.push(format!("{path}: {name}: {error}")),
            }
        }
    }

    println!(
        "{bodies} bodies, {instructions} instructions, {abstract_or_runtime} without a body, \
         {signatures} signatures, {} not decoded",
        failed.len()
    );
    for (element, count) in &unknown {
        println!("  element {element:#04x} not decoded: {count} times");
    }
    for line in failed.iter().take(20) {
        println!("  {line}");
    }
}

#[derive(Clone, Copy)]
enum SigKind {
    Method,
    Field,
    Property,
    Locals,
    Type,
}

/// Counts the element types this reader does not model, which is a more
/// useful answer than a signature that merely parsed.
fn count_unknown(ty: &TypeSig, into: &mut std::collections::BTreeMap<u8, u32>) {
    match ty {
        TypeSig::Unknown(element) => *into.entry(*element).or_default() += 1,
        TypeSig::Vector(inner)
        | TypeSig::Pointer(inner)
        | TypeSig::ByRef(inner)
        | TypeSig::Array { element: inner, .. } => count_unknown(inner, into),
        TypeSig::Generic {
            definition,
            arguments,
        } => {
            count_unknown(definition, into);
            for argument in arguments {
                count_unknown(argument, into);
            }
        }
        _ => {}
    }
}
