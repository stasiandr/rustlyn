//! The whole build hot reload gives an editor, made into `<output>`, with
//! the methods it stubs — that throw in the editor rather than run — listed
//! in `<output>/stubs.txt`: what Rustlyn does not compile yet.
//!
//! ```text
//! cargo run --release -p rustlyn-ide --example stubs -- <project> <output directory>
//! ```

use std::path::PathBuf;

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let [project, output] = arguments.as_slice() else {
        eprintln!("usage: stubs <project> <output directory>");
        std::process::exit(2);
    };
    let project = PathBuf::from(project);
    let response = rustlyn_ide::hot::Response::find(&project).unwrap_or_else(|why| panic!("{why}"));
    let generated = rustlyn_ide::hot::work_directory(&project).join("generated");
    let output = PathBuf::from(output);
    std::fs::create_dir_all(&output).expect("the output directory");
    let (built, _, _) = rustlyn_ide::hot::build_whole(
        &project,
        &response,
        &response.sources,
        &generated,
        &output.join("Assembly-CSharp.dll"),
        &Default::default(),
    )
    .unwrap_or_else(|why| panic!("{why}"));
    println!(
        "{} stubs in {} ms; see {}",
        built.stubs,
        built.milliseconds,
        output.join("stubs.txt").display()
    );
}
