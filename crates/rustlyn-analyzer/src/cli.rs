//! What the command-line tools share: printing that does not panic when the
//! reader goes away. `rustlyn-fail … | head -5` closes the pipe after five
//! lines, and `println!` answers a closed pipe with a panic and a backtrace;
//! a tool that was only read in part has nothing to report about it.

use std::io::Write;

/// Prints `text` and a line break to the standard output. A reader that has
/// gone ends the process quietly.
pub fn say(text: &str) {
    write(text, true);
}

/// Prints `text` as it is, with no line break added.
pub fn say_raw(text: &str) {
    write(text, false);
}

fn write(text: &str, newline: bool) {
    let mut out = std::io::stdout().lock();
    let done = out
        .write_all(text.as_bytes())
        .and_then(|()| {
            if newline {
                out.write_all(b"\n")
            } else {
                Ok(())
            }
        })
        .and_then(|()| out.flush());
    if let Err(error) = done {
        if error.kind() != std::io::ErrorKind::BrokenPipe {
            eprintln!("cannot write the output: {error}");
            std::process::exit(2);
        }
        std::process::exit(0);
    }
}
