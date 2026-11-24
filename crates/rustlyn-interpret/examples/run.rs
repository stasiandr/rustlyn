//! Compiles and runs a C# file.
//!
//! ```sh
//! cargo run --example run -- Program.cs
//! ```

fn main() {
    let path = std::env::args().nth(1).expect("usage: run <file.cs>");
    let source = std::fs::read_to_string(&path).expect("the file should be readable");
    match rustlyn_interpret::run(&source) {
        Ok(output) => print!("{output}"),
        Err(message) => {
            eprintln!("{message}");
            std::process::exit(1);
        }
    }
}
