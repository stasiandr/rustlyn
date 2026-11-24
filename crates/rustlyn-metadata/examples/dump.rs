//! Prints what an assembly's metadata says.
//!
//! ```sh
//! cargo run -p rustlyn-metadata --example dump -- out/Program.dll
//! ```

use rustlyn_metadata::{Assembly, table, tables};

fn main() {
    let Some(path) = std::env::args().nth(1) else {
        eprintln!("usage: dump <assembly.dll>");
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
    println!("== tables ==");
    for number in 0..64u8 {
        let rows = assembly.rows(number);
        if rows > 0 {
            println!("  {:<24} {rows}", tables::name(number));
        }
    }

    if let Some(row) = assembly.table(table::ASSEMBLY).row(1) {
        println!(
            "\n== assembly ==\n  {} {}.{}.{}.{}",
            heaps.string(row.number(7)),
            row.number(1),
            row.number(2),
            row.number(3),
            row.number(4)
        );
    }

    println!("\n== references ==");
    for row in assembly.table(table::ASSEMBLY_REF).iter() {
        println!("  {}", heaps.string(row.number(6)));
    }

    println!("\n== types ==");
    let types = assembly.table(table::TYPE_DEF);
    let fields = assembly.table(table::FIELD);
    let methods = assembly.table(table::METHOD_DEF);
    for (index, row) in types.iter().enumerate() {
        let namespace = heaps.string(row.number(2));
        let name = heaps.string(row.number(1));
        let full = if namespace.is_empty() {
            name.to_string()
        } else {
            format!("{namespace}.{name}")
        };
        println!("  {full}  flags={:#010x}", row.number(0));

        // A row says where its members begin; the next row says where they
        // end, which is why the last one runs to the end of the table.
        let next = types.row(index as u32 + 2);
        let field_range = row.number(4)..next.map_or(fields.len() + 1, |row| row.number(4));
        let method_range = row.number(5)..next.map_or(methods.len() + 1, |row| row.number(5));
        for number in field_range {
            if let Some(field) = fields.row(number) {
                println!("      field  {}", heaps.string(field.number(1)));
            }
        }
        for number in method_range {
            if let Some(method) = methods.row(number) {
                println!(
                    "      method {}  rva={:#x}",
                    heaps.string(method.number(3)),
                    method.number(0)
                );
            }
        }
    }
}
