//! Prints everything one type of an assembly says about itself.
//!
//! A type that will not load is a question about flags: whether it is
//! abstract, which interfaces it lists, which of its methods are virtual and
//! which slot each takes, and what its `MethodImpl` rows bind. `dump` shows
//! the whole assembly and none of that; this shows one type and all of it.
//!
//! ```sh
//! cargo run -p rustlyn-metadata --example inspect -- out/Program.dll LocalState
//! ```

use rustlyn_metadata::signature::{Blob, MethodSig, TypeSig};
use rustlyn_metadata::{Assembly, Token, table, tables};

fn main() {
    let mut args = std::env::args().skip(1);
    let (Some(path), Some(wanted)) = (args.next(), args.next()) else {
        eprintln!("usage: inspect <assembly.dll> <type name>");
        std::process::exit(2);
    };
    let bytes = std::fs::read(&path).unwrap_or_else(|error| {
        eprintln!("{path}: {error}");
        std::process::exit(1);
    });
    let assembly = Assembly::read(&bytes).unwrap_or_else(|error| {
        eprintln!("{path}: {error}");
        std::process::exit(1);
    });

    let heaps = assembly.heaps();
    // `#12` asks for one row of a table rather than a type: a `TypeSpec` in a
    // disassembly is a row number, and what it stands for is the question.
    if let Some(row) = wanted.strip_prefix("#")
        && let Ok(row) = row.parse::<u32>()
    {
        println!(
            "TypeSpec {row}: {}",
            name_of(
                &assembly,
                tables::TYPE_DEF_OR_REF.tables.len() as u32 - 1 + (row << 2)
            )
        );
        return;
    }
    // `member:Name` asks for every `MemberRef` of that name: what a call goes
    // through is a name, a parent and a signature, and a call that finds
    // nothing is a question about all three.
    if let Some(name) = wanted.strip_prefix("member:") {
        for (at, row) in assembly.table(table::MEMBER_REF).iter().enumerate() {
            if heaps.string(row.number(1)) != name {
                continue;
            }
            println!(
                "MemberRef {} on {}\n           {}",
                at + 1,
                name_of_member_parent(&assembly, row.number(0)),
                signature(&assembly, row.number(2))
            );
        }
        return;
    }
    // `locals:12` asks what one `StandAloneSig` row says: a body's locals are
    // one blob, and a local of the wrong type is invisible in a disassembly.
    if let Some(row) = wanted.strip_prefix("locals:")
        && let Ok(row) = row.parse::<u32>()
        && let Some(found) = assembly.table(table::STAND_ALONE_SIG).row(row)
        && let Ok(bytes) = heaps.blob(found.number(0))
    {
        match Blob::new(bytes).locals_sig() {
            Ok(locals) => {
                for (at, local) in locals.iter().enumerate() {
                    println!("  local {at}: {}", print_type(&assembly, local));
                }
            }
            Err(error) => println!("<{error:?}>"),
        }
        return;
    }
    // `types` lists every `TypeDef` with its row, which is how a runtime
    // complaint about "row 235" is turned into a name.
    // `impostors` asks which `TypeRef` rows name a type this assembly also
    // defines. Such a row is always a mistake — the runtime goes looking for
    // the name in another assembly and says only "could not load type" — and
    // nothing in a disassembly makes a `TypeRef` look different from a
    // `TypeDef`.
    if wanted == "impostors" {
        let defined: std::collections::HashSet<String> = assembly
            .table(table::TYPE_DEF)
            .iter()
            .map(|row| qualified(heaps.string(row.number(2)), heaps.string(row.number(1))))
            .collect();
        let mut found = 0usize;
        for (at, row) in assembly.table(table::TYPE_REF).iter().enumerate() {
            // A `TypeRef` whose scope is another `TypeRef` is a nested type,
            // whose simple name says nothing: half the framework has an
            // `Enumerator`. Only the ones another assembly is asked for by
            // full name can be confused with a definition here.
            if row.number(0) & 0x0003 == 3 {
                continue;
            }
            let name = qualified(heaps.string(row.number(2)), heaps.string(row.number(1)));
            if defined.contains(&name) {
                println!("TypeRef {}: {name}", at + 1);
                found += 1;
            }
        }
        println!("{found} named a type this assembly defines");
        return;
    }
    // `typerefs` says where each `TypeRef` is looked for: a scope naming the
    // module rather than an assembly sends the runtime looking in the
    // assembly being written, which has no such type.
    if wanted == "typerefs" {
        let assemblies = assembly.table(table::ASSEMBLY_REF);
        for (at, row) in assembly.table(table::TYPE_REF).iter().enumerate() {
            let scope = row.number(0);
            let (tag, index) = (scope & 0x0003, scope >> 2);
            let where_at = match tag {
                0 => "<module>".to_string(),
                2 => assemblies.row(index).map_or_else(
                    || format!("AssemblyRef {index}?"),
                    |row| heaps.string(row.number(6)).to_string(),
                ),
                3 => format!("TypeRef {index}"),
                other => format!("scope {other}:{index}"),
            };
            println!(
                "TypeRef {}: [{where_at}] {}",
                at + 1,
                qualified(heaps.string(row.number(2)), heaps.string(row.number(1)))
            );
        }
        return;
    }
    if wanted == "types" {
        for (at, row) in assembly.table(table::TYPE_DEF).iter().enumerate() {
            println!(
                "row {}: {}",
                at + 1,
                qualified(heaps.string(row.number(2)), heaps.string(row.number(1)))
            );
        }
        return;
    }
    // `byref` asks which fields hold an address: a `T&` in an ordinary class
    // is a type the runtime refuses to load, and nothing in a disassembly
    // says which field it was.
    // `holds:<text>` asks which fields have that text in their type: a
    // `ref struct` in an ordinary class is refused by the runtime, and the
    // message does not say which field it was.
    if let Some(text) = wanted.strip_prefix("holds:") {
        let types = assembly.table(table::TYPE_DEF);
        for (at, row) in assembly.table(table::FIELD).iter().enumerate() {
            let Ok(bytes) = heaps.blob(row.number(2)) else {
                continue;
            };
            let Ok(ty) = Blob::new(bytes).field_sig() else {
                continue;
            };
            let printed = print_type(&assembly, &ty);
            if !printed.contains(text) {
                continue;
            }
            let owner = types
                .iter()
                .filter(|found| found.number(4) <= at as u32 + 1)
                .map(|found| heaps.string(found.number(1)).to_string())
                .last()
                .unwrap_or_else(|| "?".to_string());
            println!(
                "field {} of {owner}: {printed}",
                heaps.string(row.number(1))
            );
        }
        return;
    }
    if wanted == "byref" {
        let types = assembly.table(table::TYPE_DEF);
        for (at, row) in assembly.table(table::FIELD).iter().enumerate() {
            let Ok(bytes) = heaps.blob(row.number(2)) else {
                continue;
            };
            let Ok(ty) = Blob::new(bytes).field_sig() else {
                continue;
            };
            if !matches!(ty, TypeSig::ByRef(_)) {
                continue;
            }
            let owner = types
                .iter()
                .filter(|found| found.number(4) <= at as u32 + 1)
                .map(|found| heaps.string(found.number(1)).to_string())
                .last()
                .unwrap_or_else(|| "?".to_string());
            println!(
                "field {} of {owner}: {}",
                heaps.string(row.number(1)),
                print_type(&assembly, &ty)
            );
        }
        return;
    }
    let types = assembly.table(table::TYPE_DEF);
    let methods = assembly.table(table::METHOD_DEF);
    let fields = assembly.table(table::FIELD);

    for (index, row) in types.iter().enumerate() {
        let name = heaps.string(row.number(1));
        let namespace = heaps.string(row.number(2));
        if name != wanted && format!("{namespace}.{name}") != wanted {
            continue;
        }
        let number = index as u32 + 1;
        println!(
            "{namespace}.{name}  (TypeDef {number})  flags={:#010x}",
            row.number(0)
        );
        println!("  extends {}", name_of(&assembly, row.number(3)));
        for (parameter, at) in generic_params(&assembly, tables::TYPE_OR_METHOD_DEF, 0, number) {
            println!("  has type parameter {parameter}");
            for constraint in constraints_on(&assembly, at) {
                println!("      constrained to {constraint}");
            }
        }

        for impl_row in assembly.table(table::INTERFACE_IMPL).iter() {
            if impl_row.number(0) == number {
                println!("  implements {}", name_of(&assembly, impl_row.number(1)));
            }
        }

        let next = types.row(number + 1);
        let field_range = row.number(4)..next.map_or(fields.len() + 1, |row| row.number(4));
        for at in field_range {
            if let Some(field) = fields.row(at) {
                println!(
                    "  field {:<40} flags={:#06x}",
                    heaps.string(field.number(1)),
                    field.number(0)
                );
            }
        }

        let method_range = row.number(5)..next.map_or(methods.len() + 1, |row| row.number(5));
        for at in method_range {
            let Some(method) = methods.row(at) else {
                continue;
            };
            println!(
                "  method {:<40} flags={:#06x} rva={:#x}  (MethodDef {at})",
                heaps.string(method.number(3)),
                method.number(2),
                method.number(0)
            );
            println!("           {}", signature(&assembly, method.number(4)));
            for (parameter, row) in generic_params(&assembly, tables::TYPE_OR_METHOD_DEF, 1, at) {
                println!("           type parameter {parameter}");
                for constraint in constraints_on(&assembly, row) {
                    println!("               constrained to {constraint}");
                }
            }
        }

        for impl_row in assembly.table(table::METHOD_IMPL).iter() {
            if impl_row.number(0) != number {
                continue;
            }
            println!(
                "  overrides {} with {}",
                method_name(&assembly, impl_row.number(2)),
                method_name(&assembly, impl_row.number(1))
            );
        }
    }
}

/// The name behind a `TypeDefOrRef` coded index.
fn name_of(assembly: &Assembly<'_>, coded: u32) -> String {
    let Some((number, row)) = tables::TYPE_DEF_OR_REF.decode(coded) else {
        return format!("<{coded:#x}>");
    };
    if row == 0 {
        return "nothing".to_string();
    }
    let heaps = assembly.heaps();
    let Some(found) = assembly.table(number).row(row) else {
        return format!("<{}[{row}]>", tables::name(number));
    };
    match number {
        table::TYPE_SPEC => match heaps.blob(found.number(0)) {
            Ok(bytes) => match Blob::new(bytes).type_sig() {
                Ok(ty) => print_type(assembly, &ty),
                Err(error) => format!("<{error:?}>"),
            },
            Err(error) => format!("<{error:?}>"),
        },
        _ => {
            let namespace = heaps.string(found.number(2));
            let name = heaps.string(found.number(1));
            if namespace.is_empty() {
                name.to_string()
            } else {
                format!("{namespace}.{name}")
            }
        }
    }
}

/// The name behind a `MethodDefOrRef` coded index.
fn method_name(assembly: &Assembly<'_>, coded: u32) -> String {
    let Some((number, row)) = tables::METHOD_DEF_OR_REF.decode(coded) else {
        return format!("<{coded:#x}>");
    };
    let heaps = assembly.heaps();
    let Some(found) = assembly.table(number).row(row) else {
        return format!("<{}[{row}]>", tables::name(number));
    };
    match number {
        table::METHOD_DEF => format!("{} (MethodDef {row})", heaps.string(found.number(3))),
        _ => format!(
            "{} on {} (MemberRef {row})",
            heaps.string(found.number(1)),
            name_of_member_parent(assembly, found.number(0))
        ),
    }
}

fn name_of_member_parent(assembly: &Assembly<'_>, coded: u32) -> String {
    let Some((number, row)) = tables::MEMBER_REF_PARENT.decode(coded) else {
        return format!("<{coded:#x}>");
    };
    let heaps = assembly.heaps();
    let Some(found) = assembly.table(number).row(row) else {
        return format!("<{}[{row}]>", tables::name(number));
    };
    match number {
        table::TYPE_SPEC => format!("TypeSpec {row}: {}", name_of(assembly, (row << 2) | 2)),
        table::METHOD_DEF => heaps.string(found.number(3)).to_string(),
        _ => {
            let namespace = heaps.string(found.number(2));
            let name = heaps.string(found.number(1));
            if namespace.is_empty() {
                name.to_string()
            } else {
                format!("{namespace}.{name}")
            }
        }
    }
}

/// The type parameters a row of `TypeDef` or `MethodDef` declares.
fn generic_params(
    assembly: &Assembly<'_>,
    coded: tables::Coded,
    tag: u32,
    row: u32,
) -> Vec<(String, u32)> {
    let heaps = assembly.heaps();
    let wanted = (row << coded.bits) | tag;
    assembly
        .table(table::GENERIC_PARAM)
        .iter()
        .enumerate()
        .filter(|(_, found)| found.number(2) == wanted)
        .map(|(at, found)| {
            (
                format!(
                    "{} ({}) flags={:#06x}",
                    heaps.string(found.number(3)),
                    found.number(0),
                    found.number(1)
                ),
                at as u32 + 1,
            )
        })
        .collect()
}

/// What a `where` clause said about one type parameter.
fn constraints_on(assembly: &Assembly<'_>, parameter: u32) -> Vec<String> {
    assembly
        .table(table::GENERIC_PARAM_CONSTRAINT)
        .iter()
        .filter(|row| row.number(0) == parameter)
        .map(|row| name_of(assembly, row.number(1)))
        .collect()
}

/// A method signature, printed the way a signature blob reads.
fn signature(assembly: &Assembly<'_>, offset: u32) -> String {
    let Ok(bytes) = assembly.heaps().blob(offset) else {
        return format!("<blob {offset}?>");
    };
    let mut blob = Blob::new(bytes);
    match blob.method_sig() {
        Ok(sig) => print_method(assembly, &sig),
        Err(error) => format!("<{error:?}>"),
    }
}

fn print_method(assembly: &Assembly<'_>, sig: &MethodSig) -> String {
    let parameters: Vec<String> = sig
        .parameters
        .iter()
        .map(|ty| print_type(assembly, ty))
        .collect();
    format!(
        "{}{} ({})",
        if sig.instance { "instance " } else { "" },
        print_type(assembly, &sig.returns),
        parameters.join(", ")
    )
}

fn print_type(assembly: &Assembly<'_>, ty: &TypeSig) -> String {
    match ty {
        TypeSig::Class(token) | TypeSig::ValueType(token) => print_token(assembly, *token),
        TypeSig::Vector(element) => format!("{}[]", print_type(assembly, element)),
        TypeSig::Array { element, rank } => {
            format!(
                "{}[{}]",
                print_type(assembly, element),
                ",".repeat(*rank as usize - 1)
            )
        }
        TypeSig::Pointer(element) => format!("{}*", print_type(assembly, element)),
        TypeSig::ByRef(element) => format!("ref {}", print_type(assembly, element)),
        TypeSig::Var(at) => format!("!{at}"),
        TypeSig::MVar(at) => format!("!!{at}"),
        TypeSig::Generic {
            definition,
            arguments,
        } => {
            let arguments: Vec<String> = arguments
                .iter()
                .map(|argument| print_type(assembly, argument))
                .collect();
            format!(
                "{}<{}>",
                print_type(assembly, definition),
                arguments.join(", ")
            )
        }
        other => format!("{other:?}"),
    }
}

/// The name behind a token a signature names, following a `TypeSpec` into the
/// signature it stands for.
fn print_token(assembly: &Assembly<'_>, token: Token) -> String {
    let number = (token.0 >> 24) as u8;
    let row = token.0 & 0x00FF_FFFF;
    let heaps = assembly.heaps();
    let Some(found) = assembly.table(number).row(row) else {
        return format!("<{}[{row}]>", tables::name(number));
    };
    if number == table::TYPE_SPEC {
        let Ok(bytes) = heaps.blob(found.number(0)) else {
            return "<a TypeSpec>".to_string();
        };
        let mut blob = Blob::new(bytes);
        return match blob.type_sig() {
            Ok(ty) => print_type(assembly, &ty),
            Err(error) => format!("<{error:?}>"),
        };
    }
    let namespace = heaps.string(found.number(2));
    let name = heaps.string(found.number(1));
    let full = if namespace.is_empty() {
        name.to_string()
    } else {
        format!("{namespace}.{name}")
    };
    format!("{full}[{} {row}]", tables::name(number))
}

/// `Namespace.Name`, or just the name where there is no namespace.
fn qualified(namespace: &str, name: &str) -> String {
    if namespace.is_empty() {
        name.to_string()
    } else {
        format!("{namespace}.{name}")
    }
}
