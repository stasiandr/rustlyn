//! Prints an assembly as C#.
//!
//! ```sh
//! cargo run -p rustlyn-decompile -- out/Program.dll [Type[::Method]] [--no-generated]
//! ```

fn main() {
    let mut path = None;
    let mut filter = None;
    let mut compiler_generated = true;
    let mut references: Option<String> = None;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--no-generated" => compiler_generated = false,
            "--references" => references = args.next(),
            _ if path.is_none() => path = Some(arg),
            _ => filter = Some(arg),
        }
    }
    let Some(path) = path else {
        eprintln!(
            "usage: decompile <assembly.dll> [Type[::Method]] [--references <dir>] [--no-generated]"
        );
        std::process::exit(2);
    };
    // Every assembly in the references directory, or next to the host's
    // shared framework when `RUSTLYN_FRAMEWORK` names it.
    let reference_dir = references.or_else(|| std::env::var("RUSTLYN_FRAMEWORK").ok());
    let mut reference_images: Vec<Vec<u8>> = Vec::new();
    if let Some(directory) = reference_dir
        && let Ok(entries) = std::fs::read_dir(&directory)
    {
        let mut paths: Vec<_> = entries
            .filter_map(|entry| entry.ok().map(|entry| entry.path()))
            .filter(|found| {
                found
                    .extension()
                    .is_some_and(|extension| extension == "dll")
            })
            .collect();
        paths.sort();
        for found in paths {
            if let Ok(image) = std::fs::read(&found) {
                reference_images.push(image);
            }
        }
    }
    let bytes = std::fs::read(&path).unwrap_or_else(|error| {
        eprintln!("{path}: {error}");
        std::process::exit(1);
    });
    // Deeply nested expressions recurse deeply; a generous stack keeps a
    // long string concatenation from being the end of the run.
    let worker = std::thread::Builder::new()
        .stack_size(512 << 20)
        .spawn(move || {
            let options = rustlyn_decompile::Options {
                compiler_generated,
                ..rustlyn_decompile::Options::default()
            };
            let images: Vec<&[u8]> = reference_images.iter().map(Vec::as_slice).collect();
            rustlyn_decompile::decompile_with_references(
                &bytes,
                &images,
                filter.as_deref(),
                &options,
            )
        })
        .expect("a thread");
    match worker.join() {
        Ok(Ok(text)) => print!("{text}"),
        Ok(Err(error)) => {
            eprintln!("{path}: {error}");
            std::process::exit(1);
        }
        Err(_) => std::process::exit(1),
    }
}
