//! Running the C# that Rustlyn can compile.
//!
//! A tree-walking interpreter over the bound tree — the same tree the IL
//! backend reads. That is the point of it being here twice: two backends that
//! agree because they are told the same thing, rather than because each was
//! carefully made to reach the same answer. It also closes the loop without a
//! runtime: `cargo run --example run` prints what the program prints, on a
//! machine with no .NET installed.

mod evaluate;
mod execute;
mod interpreter;
mod records;
mod support;
mod value;

pub use interpreter::{Interpreter, Signal};
pub use value::{Instance, Value};

use rustlyn_semantics::Compilation;
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

/// Compiles and runs a program, returning what it printed.
///
/// # Errors
///
/// Returns the compiler's diagnostics if the program does not compile, or a
/// description of what went wrong at run time.
pub fn run(source: &str) -> Result<String, String> {
    let compilation = Compilation::create(vec![parse(SourceText::new("Program.cs", source))]);

    let mut problems: Vec<_> = compilation
        .source_diagnostics()
        .iter()
        .filter(|entry| entry.diagnostic.is_error())
        .map(|entry| compilation.render(entry))
        .collect();
    problems.extend(
        compilation
            .semantic_diagnostics()
            .iter()
            .filter(|entry| entry.diagnostic.is_error())
            .map(|entry| compilation.render(entry)),
    );
    if !problems.is_empty() {
        return Err(problems.join("\n"));
    }

    let mut interpreter = Interpreter::new(&compilation);
    match interpreter.run() {
        Ok(()) => Ok(interpreter.output().to_string()),
        Err(message) => Err(message),
    }
}
