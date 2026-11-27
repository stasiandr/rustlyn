//! The tools print a line and stop; a reader that has gone is not a panic.
//! `rustlyn-fail … | head -5` closes the pipe after five lines.

use std::process::{Command, Stdio};

fn check(tool: &str, path: &str) {
    for _ in 0..5 {
        let mut child = Command::new(path)
            .arg("--help")
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap_or_else(|e| panic!("{tool}: {e}"));
        // Nobody reads: the tool's output meets a closed pipe.
        drop(child.stdout.take());
        let output = child.wait_with_output().expect("finished");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success(),
            "{tool}: {:?} {stderr}",
            output.status
        );
        assert!(!stderr.contains("panicked"), "{tool}: {stderr}");
        assert!(!stderr.contains("Broken pipe"), "{tool}: {stderr}");
    }
}

#[test]
fn a_closed_pipe_ends_every_tool_quietly() {
    check("rustlyn-blast", env!("CARGO_BIN_EXE_rustlyn-blast"));
    check("rustlyn-fail", env!("CARGO_BIN_EXE_rustlyn-fail"));
    check("rustlyn-graph", env!("CARGO_BIN_EXE_rustlyn-graph"));
    check("rustlyn-reach", env!("CARGO_BIN_EXE_rustlyn-reach"));
}
