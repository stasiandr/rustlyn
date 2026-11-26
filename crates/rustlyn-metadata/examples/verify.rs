//! Checks that every method body in an assembly has a stack that adds up.
//!
//! A runtime that refuses a body says `InvalidProgramException` and nothing
//! else — no offset, no instruction, no reason. This says all three, for every
//! body at once, which is the only way to find the one that is wrong among
//! sixty thousand that are not.
//!
//! ```sh
//! cargo run -p rustlyn-metadata --example verify -- out/Program.dll
//! cargo run -p rustlyn-metadata --example verify -- out/Program.dll PreLex
//! ```

use rustlyn_metadata::{Assembly, Body, table, verify};

fn main() -> std::process::ExitCode {
    let Some(path) = std::env::args().nth(1) else {
        eprintln!("usage: verify <assembly.dll> [type or method name]");
        return std::process::ExitCode::FAILURE;
    };
    let filter = std::env::args().nth(2);
    let bytes = std::fs::read(&path).unwrap_or_else(|error| {
        eprintln!("{path}: {error}");
        std::process::exit(1);
    });
    let assembly = Assembly::read(&bytes).unwrap_or_else(|error| {
        eprintln!("{path}: {error}");
        std::process::exit(1);
    });

    let heaps = assembly.heaps();
    let types = assembly.table(table::TYPE_DEF);
    let methods = assembly.table(table::METHOD_DEF);
    // How many type parameters each type and each method declares, which is
    // what says whether a `!0` in one of its bodies means anything.
    let mut type_arity: std::collections::HashMap<u32, usize> = std::collections::HashMap::new();
    let mut method_arity: std::collections::HashMap<u32, usize> = std::collections::HashMap::new();
    for row in assembly.table(table::GENERIC_PARAM).iter() {
        let owner = row.token(2);
        let counts = if owner.table() == table::TYPE_DEF {
            &mut type_arity
        } else {
            &mut method_arity
        };
        *counts.entry(owner.row()).or_default() += 1;
    }
    let mut checked = 0usize;
    let mut refused = 0usize;

    for (index, ty) in types.iter().enumerate() {
        let name = heaps.string(ty.number(1));
        let next = types.row(index as u32 + 2);
        let range = ty.number(5)..next.map_or(methods.len() + 1, |row| row.number(5));
        for number in range {
            let Some(method) = methods.row(number) else {
                continue;
            };
            let full = format!("{name}::{}", heaps.string(method.number(3)));
            if filter.as_ref().is_some_and(|want| !full.contains(want)) {
                continue;
            }
            let rva = method.number(0);
            if rva == 0 {
                continue;
            }
            let Ok(rest) = assembly.image().from_rva(rva) else {
                println!("{full}: address {rva:#x} is in no section");
                refused += 1;
                continue;
            };
            let body = match Body::read(rest) {
                Ok(body) => body,
                Err(error) => {
                    println!("{full}: {error}");
                    refused += 1;
                    continue;
                }
            };
            checked += 1;
            let mut complaints = verify::stack(&assembly, &body);
            complaints.extend(verify::definitions(&assembly, &body, index as u32 + 1));
            complaints.extend(verify::scopes(
                &assembly,
                &body,
                type_arity
                    .get(&(index as u32 + 1))
                    .copied()
                    .unwrap_or_default(),
                method_arity.get(&number).copied().unwrap_or_default(),
            ));
            if complaints.is_empty() {
                continue;
            }
            refused += 1;
            println!("{full}  (MethodDef {number})");
            for complaint in complaints {
                println!("  IL_{:04x}: {}", complaint.offset, complaint.message);
            }
        }
    }

    // Every construction in the assembly, once: a wrong argument count is
    // nothing to do with a body, and the runtime that refuses one says only
    // `BadImageFormatException`.
    if filter.is_none() {
        for complaint in verify::arities(&assembly) {
            println!("{complaint}");
            refused += 1;
        }
    }

    println!("{checked} bodies checked, {refused} do not match");
    if refused == 0 {
        std::process::ExitCode::SUCCESS
    } else {
        std::process::ExitCode::FAILURE
    }
}
