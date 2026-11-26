//! Prints the IL of every method in an assembly, the way `ildasm` does.
//!
//! ```sh
//! cargo run -p rustlyn-metadata --example disasm -- out/Program.dll
//! ```

use rustlyn_metadata::body::{Handler, Value};
use rustlyn_metadata::{Assembly, Body, Token, table, tables};

fn main() {
    let Some(path) = std::env::args().nth(1) else {
        eprintln!("usage: disasm <assembly.dll> [type or method name]");
        std::process::exit(2);
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

    for (index, ty) in types.iter().enumerate() {
        let name = heaps.string(ty.number(1));
        let next = types.row(index as u32 + 2);
        let range = ty.number(5)..next.map_or(methods.len() + 1, |row| row.number(5));
        for number in range {
            let Some(method) = methods.row(number) else {
                continue;
            };
            let method_name = heaps.string(method.number(3));
            let full = format!("{name}::{method_name}");
            if filter.as_ref().is_some_and(|want| !full.contains(want)) {
                continue;
            }
            let rva = method.number(0);
            if rva == 0 {
                println!("\n.method {full}  // no body");
                continue;
            }
            print_body(&assembly, &full, rva);
        }
    }
}

fn print_body(assembly: &Assembly<'_>, name: &str, rva: u32) {
    // A body has no length until its header is read, so take what is left of
    // the section and let the header say how much of it to use.
    let Ok(rest) = assembly.image().from_rva(rva) else {
        println!("\n.method {name}  // address {rva:#x} is in no section");
        return;
    };
    let body = match Body::read(rest) {
        Ok(body) => body,
        Err(error) => {
            println!("\n.method {name}  // {error}");
            return;
        }
    };

    println!("\n.method {name}");
    println!("  .maxstack {}", body.max_stack);
    if let Some(locals) = body.locals {
        println!(
            "  .locals {}{:?}",
            if body.init_locals { "init " } else { "" },
            locals
        );
    }
    for region in &body.regions {
        let what = match region.kind {
            Handler::Catch(token) => format!("catch {}", describe(assembly, token)),
            Handler::Filter(at) => format!("filter IL_{at:04x}"),
            Handler::Finally => "finally".to_string(),
            Handler::Fault => "fault".to_string(),
        };
        println!(
            "  .try IL_{:04x}..IL_{:04x} {what} IL_{:04x}..IL_{:04x}",
            region.try_offset,
            region.try_offset + region.try_length,
            region.handler_offset,
            region.handler_offset + region.handler_length,
        );
    }
    for instruction in &body.instructions {
        let operand = match &instruction.value {
            Value::None => String::new(),
            Value::Variable(index) => format!(" {index}"),
            Value::Int(value) => format!(" {value}"),
            Value::Float(value) => format!(" {value}"),
            Value::Token(token) => format!(" {}", describe(assembly, *token)),
            Value::Target(at) => format!(" IL_{at:04x}"),
            Value::Targets(targets) => {
                let names: Vec<String> = targets.iter().map(|at| format!("IL_{at:04x}")).collect();
                format!(" ({})", names.join(", "))
            }
        };
        println!(
            "  IL_{:04x}:  {}{operand}",
            instruction.offset, instruction.name
        );
    }
}

/// What a token in an instruction points at, by name where there is one.
fn describe(assembly: &Assembly<'_>, token: Token) -> String {
    let heaps = assembly.heaps();
    // A `ldstr` token is an offset into `#US` rather than a row anywhere.
    if token.table() == 0x70 {
        return match heaps.user_string(token.row()) {
            Ok(text) => format!("{text:?}"),
            Err(_) => format!("{token:?}"),
        };
    }
    let Some(row) = assembly.row(token) else {
        return format!("{token:?}");
    };
    let named = |column: usize| heaps.string(row.number(column)).to_string();
    match token.table() {
        table::TYPE_DEF => {
            let namespace = named(2);
            let name = named(1);
            if namespace.is_empty() {
                name
            } else {
                format!("{namespace}.{name}")
            }
        }
        table::TYPE_REF => {
            let namespace = named(2);
            let name = named(1);
            let scope = describe(assembly, row.token(0));
            if namespace.is_empty() {
                format!("[{scope}]{name}")
            } else {
                format!("[{scope}]{namespace}.{name}")
            }
        }
        // The row is part of the answer: two methods of a type can share a
        // name, and which one a call went to is the question.
        table::METHOD_DEF => format!("{} (MethodDef {})", named(3), token.row()),
        table::FIELD | table::MEMBER_REF => {
            let owner = if token.table() == table::MEMBER_REF {
                format!("{}::", describe(assembly, row.token(0)))
            } else {
                String::new()
            };
            format!(
                "{owner}{} ({} {})",
                named(1),
                tables::name(token.table()),
                token.row()
            )
        }
        table::ASSEMBLY_REF => named(6),
        table::MODULE => named(1),
        _ => format!("{}({})", tables::name(token.table()), token.row()),
    }
}
