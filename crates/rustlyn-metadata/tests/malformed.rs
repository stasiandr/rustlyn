//! A damaged assembly is an error, not a crash and not a wait without end.
//!
//! A reference assembly is a file from somewhere else: half written by an
//! interrupted build, cut short by a full disk, or made by someone who wants
//! the compiler — or the editor that has it loaded — gone. Every number in
//! it is a claim: a count of rows, a length, an offset, how many cases a
//! `switch` has. Reading has to check each against the bytes that are there.

use rustlyn_metadata::{Assembly, Blob, Body, Error, Token, table};
use rustlyn_semantics::Compilation;
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

/// An assembly with a bit of everything the reader reads: fields,
/// properties, generics, exception clauses, a `switch`, locals.
fn sample() -> Vec<u8> {
    let source = r#"
using System;
using System.Collections.Generic;

interface IShape { double Area { get; } }

struct Point { public int X; public int Y; }

class Box<T> : IShape where T : struct
{
    T _held;
    public double Area => 1.5;
    public T Held { get => _held; set => _held = value; }
}

static class Program
{
    static int Pick(int n)
    {
        switch (n)
        {
            case 0: return 10;
            case 1: return 11;
            case 2: return 12;
            case 3: return 13;
            default: return -1;
        }
    }

    static int Guarded(int n)
    {
        var total = 0;
        try
        {
            if (n > 3) throw new ArgumentException("bad");
            total += n;
        }
        catch (ArgumentException e)
        {
            total = e.Message.Length;
        }
        finally
        {
            total += 1;
        }
        return total;
    }

    static void Main()
    {
        var box = new Box<Point>();
        box.Held = new Point { X = 1, Y = 2 };
        var items = new[] { new[] { 1, 2, 3 }, new[] { 4 } };
        long sum = 0;
        foreach (var item in items) foreach (var n in item) sum += Pick(n);
        Console.WriteLine(sum + Guarded(4) + (long)box.Area + box.Held.X);
    }
}
"#;
    let compilation = Compilation::create(vec![parse(SourceText::new("Program.cs", source))]);
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "the sample: {diagnostics:#?}");
    rustlyn_emit::emit(&compilation, "Sample")
        .unwrap_or_else(|error| panic!("the sample: {error}"))
        .assembly
}

/// Reads everything the reader can read out of `bytes`: every column of
/// every row, every heap entry a column names, every signature, every
/// method body. What it finds does not matter; that it comes back does.
fn walk(bytes: &[u8]) -> Result<(), Error> {
    let assembly = Assembly::read(bytes)?;
    let heaps = assembly.heaps();
    for number in 0..=u8::MAX {
        let rows = assembly.table(number);
        assert_eq!(rows.len(), assembly.rows(number));
        for row in rows.iter() {
            for (column, kind) in rustlyn_metadata::tables::columns(number).iter().enumerate() {
                let value = row.number(column);
                match kind {
                    rustlyn_metadata::Column::String => {
                        let _ = heaps.string(value);
                    }
                    rustlyn_metadata::Column::Guid => {
                        let _ = heaps.guid(value);
                    }
                    rustlyn_metadata::Column::Blob => {
                        if let Ok(blob) = heaps.blob(value) {
                            // Whatever kind of signature it is, each reading
                            // of it has to come back.
                            let _ = Blob::new(blob).method_sig();
                            let _ = Blob::new(blob).field_sig();
                            let _ = Blob::new(blob).property_sig();
                            let _ = Blob::new(blob).locals_sig();
                            let _ = Blob::new(blob).type_sig();
                        }
                    }
                    _ => {
                        // A token names a row of any table, existing or not.
                        let token = row.token(column);
                        let _ = assembly.row(token);
                        let _ = assembly.row(Token(value));
                        let _ = heaps.user_string(value);
                    }
                }
            }
        }
    }
    for method in assembly.table(table::METHOD_DEF).iter() {
        let rva = method.number(0);
        if rva == 0 {
            continue;
        }
        if let Ok(code) = assembly.image().from_rva(rva) {
            let _ = Body::read(code);
        }
        let _ = assembly.image().at_rva(rva, usize::MAX);
    }
    let _ = assembly.row(assembly.entry_point);
    Ok(())
}

/// Runs `work` and fails if it has not come back in `seconds`: a reader that
/// walks a count instead of the bytes does not crash, it just never ends.
fn within(seconds: u64, work: impl FnOnce() + Send + 'static) {
    let (done, finished) = std::sync::mpsc::channel();
    let worker = std::thread::Builder::new()
        .stack_size(8 << 20)
        .spawn(move || {
            work();
            let _ = done.send(());
        })
        .expect("a thread to read on");
    match finished.recv_timeout(std::time::Duration::from_secs(seconds)) {
        Ok(()) => worker.join().expect("the reading"),
        // The sender is gone without a word: the reading panicked.
        Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
            std::panic::resume_unwind(worker.join().expect_err("the reading panicked"));
        }
        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
            panic!("reading had not finished after {seconds} seconds")
        }
    }
}

/// A small generator with a fixed seed: the same damage every run.
struct Random(u64);

impl Random {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, bound: usize) -> usize {
        (self.next() % bound as u64) as usize
    }
}

#[test]
fn the_sample_reads_whole() {
    let bytes = sample();
    within(60, move || walk(&bytes).expect("the sample as emitted"));
}

#[test]
fn a_file_cut_short_anywhere_is_an_error_or_reads() {
    let bytes = sample();
    within(120, move || {
        for length in 0..bytes.len() {
            let _ = walk(&bytes[..length]);
        }
    });
}

#[test]
fn damaged_bytes_never_crash_or_hang_the_reader() {
    let bytes = sample();
    within(300, move || {
        let mut random = Random(0x9E37_79B9_7F4A_7C15);
        // The values damage tends to be: nothing, everything, a sign bit, a
        // count one too many.
        let telling = [0x00, 0xFF, 0x80, 0x7F, 0x01, 0x40, 0xFE, 0x20];
        for _ in 0..30_000 {
            let mut damaged = bytes.clone();
            for _ in 0..=random.below(4) {
                let at = random.below(damaged.len());
                match random.below(4) {
                    0 => damaged[at] = telling[random.below(telling.len())],
                    1 => damaged[at] = random.next() as u8,
                    2 => damaged[at] ^= 1 << random.below(8),
                    // A whole word of ones or zeros: an offset or a count
                    // gone wild.
                    _ => {
                        let fill = if random.below(2) == 0 { 0x00 } else { 0xFF };
                        for byte in damaged.iter_mut().skip(at).take(4) {
                            *byte = fill;
                        }
                    }
                }
            }
            let _ = walk(&damaged);
        }
    });
}

/// Where the table stream (`#~`) starts in the file.
fn table_stream(bytes: &[u8]) -> usize {
    let root = bytes
        .windows(4)
        .position(|window| window == b"BSJB")
        .expect("a metadata root");
    let name = bytes[root..]
        .windows(3)
        .position(|window| window == b"#~\0")
        .expect("a table stream");
    let header = root + name - 8;
    let offset = u32::from_le_bytes(bytes[header..header + 4].try_into().expect("four bytes"));
    root + offset as usize
}

#[test]
fn a_row_count_past_the_end_of_the_file_is_an_error() {
    // The first row count is the `Module` table's: one row, in every
    // assembly. Four thousand million of them were walked one by one.
    let mut bytes = sample();
    let counts = table_stream(&bytes) + 24;
    bytes[counts..counts + 4].copy_from_slice(&u32::MAX.to_le_bytes());
    within(30, move || {
        assert_eq!(walk(&bytes), Err(Error::Truncated));
    });
}

#[test]
fn rows_in_a_table_that_does_not_exist_are_an_error() {
    // Table 0x3F is no table: its rows have no width, so any number of them
    // fit in no bytes at all, and the walk over them never ended.
    let mut bytes = sample();
    let stream = table_stream(&bytes);
    let valid = u64::from_le_bytes(bytes[stream + 8..stream + 16].try_into().expect("eight"));
    let present = valid.count_ones() as usize;
    bytes[stream + 8..stream + 16].copy_from_slice(&(valid | 1 << 63).to_le_bytes());
    // Its count goes after the others', over the first row of the first
    // table — which is as damaged as the rest of this file now is.
    let count = stream + 24 + 4 * present;
    bytes[count..count + 4].copy_from_slice(&u32::MAX.to_le_bytes());
    within(30, move || {
        // Malformed, or cut short where the count pushed the rows of the
        // real tables past the end: an error either way, and at once.
        assert!(matches!(
            walk(&bytes),
            Err(Error::Malformed(_) | Error::Truncated)
        ));
    });
}

#[test]
fn a_method_data_section_of_no_size_is_an_error() {
    // A fat header, one `ret`, and a section that says another follows it
    // zero bytes on: itself, for ever.
    let mut body = vec![0x1B, 0x30, 0x08, 0x00, 0x01, 0x00, 0x00, 0x00, 0, 0, 0, 0];
    body.extend_from_slice(&[0x2A, 0, 0, 0]);
    body.extend_from_slice(&[0x80, 0x00, 0x00, 0x00]);
    within(30, move || {
        assert!(matches!(Body::read(&body), Err(Error::Malformed(_))));
    });
    // And one whose header the file ends in the middle of.
    let cut = [
        0x1B, 0x30, 0x08, 0x00, 0x01, 0x00, 0x00, 0x00, 0, 0, 0, 0, 0x2A, 0, 0, 0, 0x41,
    ];
    assert_eq!(Body::read(&cut), Err(Error::Truncated));
}

#[test]
fn a_switch_counting_more_cases_than_there_are_bytes_is_an_error() {
    // `switch` with 0xFFFFFFFF cases, in a tiny body of five bytes: room for
    // sixteen gigabytes of targets was asked for before the first was read.
    let body = [5 << 2 | 0x02, 0x45, 0xFF, 0xFF, 0xFF, 0xFF];
    assert_eq!(Body::read(&body), Err(Error::Truncated));
}

#[test]
fn a_signature_nested_without_end_is_an_error() {
    // A megabyte of `PTR`: each is a call deeper.
    let pointers = vec![0x0F; 1 << 20];
    within(30, move || {
        assert!(matches!(
            Blob::new(&pointers).type_sig(),
            Err(Error::Malformed(_))
        ));
        // A handful deep is a type.
        assert!(Blob::new(&[0x0F, 0x0F, 0x1D, 0x08]).type_sig().is_ok());
    });
}

#[test]
fn a_signature_counting_more_parameters_than_it_has_is_an_error() {
    // The default convention, 0x1FFFFFFF parameters, `void`, and the end.
    let signature = [0x00, 0xDF, 0xFF, 0xFF, 0xFF, 0x01];
    assert_eq!(Blob::new(&signature).method_sig(), Err(Error::Truncated));
    assert_eq!(
        Blob::new(&[0x07, 0xDF, 0xFF, 0xFF, 0xFF]).locals_sig(),
        Err(Error::Truncated)
    );
    // `List<…>` with as many arguments.
    assert_eq!(
        Blob::new(&[0x15, 0x12, 0x05, 0xDF, 0xFF, 0xFF, 0xFF]).type_sig(),
        Err(Error::Truncated)
    );
}

/// The same damage, read by the compiler as a reference: what the reader
/// lets through, the loader has to make sense of or leave. A `TypeRef` whose
/// enclosing type was itself was followed for ever.
#[test]
fn a_damaged_reference_never_crashes_or_hangs_the_compiler() {
    let library = r#"
using System;
public interface IShape { double Area { get; } }
public struct Point { public int X; public int Y; }
public enum Colour { Red, Green = 5 }
public class Base { public virtual int F(int x) => x; protected int P; public const int K = 3; }
public class Box<T> : Base, IShape where T : struct
{
    T _held;
    public double Area => 1.5;
    public T Held { get => _held; set => _held = value; }
    public override int F(int x) => x + 1;
    public static Box<T> operator +(Box<T> a, Box<T> b) => a;
    public class Inner { public int[] Items; }
}
public static class Program
{
    public static int Pick(int n, Colour c = Colour.Green) { return n; }
    static void Main() { Console.WriteLine(Pick(1)); }
}
"#;
    let user = "class U : Base { void M() { var b = new Box<Point>(); \
                b.Held = new Point { X = 1 }; var i = new Box<Point>.Inner(); \
                int k = Program.Pick(b.F(Base.K), Colour.Red) + i.Items.Length; \
                IShape s = b; double a = s.Area; var c = b + b; } }";
    let compilation = Compilation::create(vec![parse(SourceText::new("Lib.cs", library))]);
    let bytes = rustlyn_emit::emit(&compilation, "Lib")
        .unwrap_or_else(|error| panic!("the library: {error}"))
        .assembly;
    within(600, move || {
        let mut random = Random(0x1234_5678_9ABC_DEF1);
        let telling = [0x00, 0xFF, 0x80, 0x7F, 0x01, 0x40, 0xFE, 0x20];
        for _ in 0..3_000 {
            let mut damaged = bytes.clone();
            for _ in 0..=random.below(3) {
                let at = random.below(damaged.len());
                match random.below(3) {
                    0 => damaged[at] = telling[random.below(telling.len())],
                    1 => damaged[at] = random.next() as u8,
                    _ => damaged[at] ^= 1 << random.below(8),
                }
            }
            let compilation = Compilation::create_with_references(
                vec![parse(SourceText::new("U.cs", user))],
                &[&damaged],
            );
            let _ = compilation.semantic_diagnostics();
        }
    });
}
