//! Compiling against real assemblies and running what comes out.
//!
//! The rest of the emitter's tests compile against the synthesised core
//! library: three hundred lines of C# standing in for `System.Runtime`, good
//! enough to bind against and never loaded by anything. These compile against
//! the same files the program will run on, which is the only way to find out
//! whether the symbols a loader built agree with the assembly a runtime opens.

use std::path::{Path, PathBuf};
use std::process::Command;

use rustlyn_semantics::Compilation;
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

/// The .NET host, or `None` when there is none — unless
/// `RUSTLYN_REQUIRE_DOTNET` is set, as CI sets it: there a missing host is a
/// broken setup, and a test that only compiled must not pass as one that ran.
fn host() -> Option<PathBuf> {
    let found = find_host();
    assert!(
        found.is_some() || std::env::var_os("RUSTLYN_REQUIRE_DOTNET").is_none(),
        "RUSTLYN_REQUIRE_DOTNET is set, but no .NET host was found"
    );
    found
}

/// The .NET host to run assemblies with, if there is one.
///
/// `RUSTLYN_DOTNET` wins, then `DOTNET_ROOT`, then the path, then the place a
/// manual install puts it.
fn find_host() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("RUSTLYN_DOTNET") {
        let path = PathBuf::from(path);
        return path.exists().then_some(path);
    }
    let mut roots: Vec<PathBuf> = Vec::new();
    if let Ok(root) = std::env::var("DOTNET_ROOT") {
        roots.push(PathBuf::from(root));
    }
    if let Ok(paths) = std::env::var("PATH") {
        roots.extend(std::env::split_paths(&paths));
    }
    if let Ok(home) = std::env::var("HOME") {
        roots.push(PathBuf::from(home).join("dotnet"));
    }
    // A `dotnet` on the path may be a link to the install (Homebrew's
    // `/opt/homebrew/bin/dotnet`), and the framework is beside the install.
    roots
        .into_iter()
        .map(|directory| directory.join("dotnet"))
        .find(|candidate| candidate.is_file())
        .map(|candidate| std::fs::canonicalize(&candidate).unwrap_or(candidate))
}

/// The shared framework the program will be compiled and run against.
fn framework() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("RUSTLYN_FRAMEWORK") {
        let path = PathBuf::from(path);
        return path.is_dir().then_some(path);
    }
    let root = host()?.parent()?.to_path_buf();
    let mut versions: Vec<_> = std::fs::read_dir(root.join("shared/Microsoft.NETCore.App"))
        .ok()?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.is_dir())
        .collect();
    // By version, not by text: `10.0.12` is newer than `8.0.31`.
    versions.sort_by_key(|path| {
        path.file_name()
            .and_then(|name| name.to_str())
            .map(|name| {
                name.split(['.', '-'])
                    .map(|part| part.parse::<u32>().unwrap_or(0))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default()
    });
    versions.pop()
}

/// Everything in the framework, which is what `-r` would have named.
fn references() -> Option<Vec<Vec<u8>>> {
    let mut paths: Vec<_> = std::fs::read_dir(framework()?)
        .ok()?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|extension| extension == "dll"))
        .collect();
    paths.sort();
    Some(
        paths
            .iter()
            .filter_map(|path| std::fs::read(path).ok())
            .collect(),
    )
}

/// Runs a program to its end and returns what it printed, or fails the test
/// once it has run two minutes: a program the compiler got wrong may loop
/// for ever, and that has to fail one test, not hang the run.
fn output_within(command: &mut Command) -> std::process::Output {
    use std::io::Read;
    let mut child = command
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("the .NET host should be runnable");
    let mut stdout = child.stdout.take().expect("piped");
    let mut stderr = child.stderr.take().expect("piped");
    let out = std::thread::spawn(move || {
        let mut bytes = Vec::new();
        let _ = stdout.read_to_end(&mut bytes);
        bytes
    });
    let err = std::thread::spawn(move || {
        let mut bytes = Vec::new();
        let _ = stderr.read_to_end(&mut bytes);
        bytes
    });
    let started = std::time::Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().expect("waitable") {
            break status;
        }
        if started.elapsed() > std::time::Duration::from_secs(120) {
            let _ = child.kill();
            let _ = child.wait();
            panic!("the program did not finish in two minutes");
        }
        std::thread::sleep(std::time::Duration::from_millis(20));
    };
    std::process::Output {
        status,
        stdout: out.join().expect("read"),
        stderr: err.join().expect("read"),
    }
}

fn scratch(name: &str) -> PathBuf {
    let directory = std::env::temp_dir().join(format!("rustlyn-references-{name}"));
    let _ = std::fs::remove_dir_all(&directory);
    std::fs::create_dir_all(&directory).expect("a temporary directory should be creatable");
    directory
}

fn run(assembly: &Path) -> String {
    let host = host().expect("a host, since the framework was found through it");
    // On macOS .NET 10 formats by the region the system settings name
    // (`1,5` under a Georgian one) unless the environment names a locale;
    // the expected output is written in en-US.
    let mut command = Command::new(&host);
    if cfg!(target_os = "macos") && std::env::var_os("LC_ALL").is_none() {
        command.env("LC_ALL", "en_US.UTF-8");
    }
    let output = output_within(command.arg(assembly));
    assert!(
        output.status.success(),
        "{} failed: {}{}",
        assembly.display(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).replace("\r\n", "\n")
}

/// Compiles `source` against the real framework, runs it and compares.
#[track_caller]
fn check(name: &str, source: &str, expected: &str) {
    check_with_resources(name, source, &[], expected);
}

/// As [`check`], with these resources embedded in the assembly.
fn check_with_resources(
    name: &str,
    source: &str,
    resources: &[rustlyn_emit::Resource],
    expected: &str,
) {
    let Some(bytes) = references() else {
        println!("note: {name} was skipped; no .NET shared framework was found");
        return;
    };
    let compilation = compiled(name, source, &bytes);
    let emitted = rustlyn_emit::emit_with_resources(&compilation, name, resources)
        .unwrap_or_else(|error| panic!("{name} could not be emitted: {error}"));
    let directory = scratch(name);
    run_emitted(name, &directory, &emitted, expected);
    if resources.is_empty() && std::env::var_os("RUSTLYN_ROUNDTRIP").is_some() {
        roundtrip(name, &emitted.assembly, &bytes, expected);
    }
}

/// The programs the decompiler does not yet read back into C# that compiles
/// again and prints the same, one name per line. What is not listed has to:
/// a program that starts to pass comes off the list, and one that stops
/// passing is a regression.
const ROUNDTRIP_KNOWN: &str = include_str!("roundtrip_known.txt");

/// The program read back by the decompiler, compiled again and run: it has
/// to print what the original did. Under `RUSTLYN_ROUNDTRIP=all` the known
/// failures are tried too, and the ones that now pass say so.
fn roundtrip(name: &str, assembly: &[u8], bytes: &[Vec<u8>], expected: &str) {
    let known = ROUNDTRIP_KNOWN.lines().any(|line| line.trim() == name);
    let all = std::env::var("RUSTLYN_ROUNDTRIP").is_ok_and(|value| value == "all");
    if known && !all {
        return;
    }
    let passed = std::panic::catch_unwind(|| roundtrip_unlisted(name, assembly, bytes, expected));
    match passed {
        Ok(()) if known => println!("ROUNDTRIP-FIXED {name}: take it off roundtrip_known.txt"),
        Ok(()) => {}
        Err(_) if known => {}
        Err(panic) => std::panic::resume_unwind(panic),
    }
}

fn roundtrip_unlisted(name: &str, assembly: &[u8], bytes: &[Vec<u8>], expected: &str) {
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
    let text = rustlyn_decompile::decompile_with_references(
        assembly,
        &images,
        None,
        &rustlyn_decompile::Options::default(),
    )
    .unwrap_or_else(|error| panic!("ROUNDTRIP-READ {name}: {error}"));
    let again = format!("{name}Again");
    let directory = scratch(&again);
    std::fs::write(directory.join("Program.cs"), &text).expect("writable");
    let result = std::panic::catch_unwind(|| {
        let compilation = compiled(&again, &text, bytes);
        rustlyn_emit::emit(&compilation, &again)
            .unwrap_or_else(|error| panic!("could not be emitted: {error}"))
    });
    let Ok(emitted) = result else {
        panic!("ROUNDTRIP-COMPILE {name}: see {}", directory.display());
    };
    run_emitted(&again, &directory, &emitted, expected);
}

/// As [`check`], with `library` compiled first into an assembly of its own
/// that the program references and runs beside.
#[track_caller]
fn check_with_library(name: &str, library: &str, source: &str, expected: &str) {
    let Some(mut bytes) = references() else {
        println!("note: {name} was skipped; no .NET shared framework was found");
        return;
    };
    let directory = scratch(name);
    let library_name = format!("{name}Library");
    let compilation = compiled(&library_name, library, &bytes);
    let emitted = rustlyn_emit::emit_library(&compilation, &library_name)
        .unwrap_or_else(|error| panic!("{library_name} could not be emitted: {error}"));
    std::fs::write(
        directory.join(format!("{library_name}.dll")),
        &emitted.assembly,
    )
    .expect("the library should be writable");
    bytes.push(emitted.assembly);
    let compilation = compiled(name, source, &bytes);
    let emitted = rustlyn_emit::emit(&compilation, name)
        .unwrap_or_else(|error| panic!("{name} could not be emitted: {error}"));
    run_emitted(name, &directory, &emitted, expected);
}

/// `source` bound against these assemblies, which it has to compile cleanly
/// against.
fn compiled(name: &str, source: &str, bytes: &[Vec<u8>]) -> Compilation {
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
    let compilation = Compilation::create_with_references(
        vec![parse(SourceText::new("Program.cs", source))],
        &images,
    );
    let diagnostics: Vec<String> = compilation
        .source_diagnostics()
        .into_iter()
        .map(|entry| compilation.render(entry))
        // A warning is no failure to compile: the programs here may well
        // have something Roslyn warns about.
        .chain(
            compilation
                .semantic_diagnostics()
                .iter()
                .filter(|entry| entry.diagnostic.is_error())
                .map(|entry| compilation.render(entry)),
        )
        .collect();
    assert!(
        diagnostics.is_empty(),
        "{name} did not compile: {diagnostics:#?}"
    );
    compilation
}

/// Writes an emitted program into `directory`, runs it and compares.
fn run_emitted(name: &str, directory: &Path, emitted: &rustlyn_emit::Emitted, expected: &str) {
    let assembly = directory.join(format!("{name}.dll"));
    std::fs::write(&assembly, &emitted.assembly).expect("the assembly should be writable");
    // The emitted configuration asks for the references' major version; the
    // host will not roll a release request forward to a preview build, so
    // the exact framework the references came from is named instead.
    let config = match framework().and_then(|path| {
        path.file_name()
            .map(|name| name.to_string_lossy().into_owned())
    }) {
        Some(version) => {
            let major = version.split('.').next().unwrap_or("8");
            format!(
                r#"{{"runtimeOptions":{{"tfm":"net{major}.0","framework":{{"name":"Microsoft.NETCore.App","version":"{version}"}}}}}}"#
            )
        }
        None => emitted.runtime_config.clone(),
    };
    std::fs::write(directory.join(format!("{name}.runtimeconfig.json")), config)
        .expect("the runtime configuration should be writable");
    assert_eq!(run(&assembly), expected, "{name} printed the wrong thing");
}

#[test]
fn hello_against_the_real_framework() {
    check(
        "RefHello",
        r#"
using System;
class RefHello
{
    static void Main() { Console.WriteLine("hello"); }
}
"#,
        "hello\n",
    );
}

#[test]
fn a_generic_collection_against_the_real_framework() {
    check(
        "RefList",
        r#"
using System;
using System.Collections.Generic;
class RefList
{
    static void Main()
    {
        List<string> names = new List<string>();
        names.Add("world");
        names.Add("again");
        foreach (string name in names)
        {
            Console.WriteLine("hello, " + name);
        }
        Console.WriteLine(names.Count);
    }
}
"#,
        "hello, world\nhello, again\n2\n",
    );
}

#[test]
fn a_program_that_uses_a_good_deal_of_the_framework() {
    check(
        "RefMixed",
        r#"
using System;
using System.Collections.Generic;

interface IShape
{
    double Area();
}

struct Point
{
    public int X;
    public int Y;
    public Point(int x, int y) { X = x; Y = y; }
    public override string ToString() { return "(" + X + ", " + Y + ")"; }
}

class Square : IShape
{
    private double side;
    public Square(double side) { this.side = side; }
    public double Area() { return side * side; }
    public override string ToString() { return "square " + Area(); }
}

class RefMixed
{
    static T Last<T>(List<T> items) { return items[items.Count - 1]; }

    static void Main()
    {
        Point p = new Point(3, 4);
        Console.WriteLine(p);
        Console.WriteLine(p.X + p.Y);

        IShape shape = new Square(2.5);
        Console.WriteLine(shape);
        Console.WriteLine(shape.Area());

        int[] numbers = new int[] { 5, 3, 9, 1 };
        int total = 0;
        foreach (int n in numbers) { total += n; }
        Console.WriteLine(total);
        Console.WriteLine(numbers.Length);

        List<string> words = new List<string>();
        words.Add("alpha");
        words.Add("omega");
        Console.WriteLine(Last<string>(words));

        Dictionary<string, int> counts = new Dictionary<string, int>();
        counts["one"] = 1;
        counts["two"] = 2;
        Console.WriteLine(counts["two"]);
        Console.WriteLine(counts.Count);

        string text = "42";
        Console.WriteLine(int.Parse(text) * 2);
        Console.WriteLine(text.Length);
        Console.WriteLine("ALPHA".ToLower());

        try
        {
            throw new InvalidOperationException("boom");
        }
        catch (InvalidOperationException e)
        {
            Console.WriteLine("caught " + e.Message);
        }
        finally
        {
            Console.WriteLine("done");
        }

        Func<int, int> twice = x => x * 2;
        Console.WriteLine(twice(21));
    }
}
"#,
        "(3, 4)\n7\nsquare 6.25\n6.25\n18\n4\nomega\n2\n2\n84\n2\nalpha\ncaught boom\ndone\n42\n",
    );
}

#[test]
fn linq_against_the_real_framework() {
    check(
        "RefLinq",
        r#"
using System;
using System.Collections.Generic;
using System.Linq;

class RefLinq
{
    static void Main()
    {
        List<int> numbers = new List<int>();
        numbers.Add(3);
        numbers.Add(1);
        numbers.Add(2);

        Console.WriteLine(numbers.Count());
        Console.WriteLine(numbers.First());
        Console.WriteLine(numbers.Last());
        Console.WriteLine(numbers.Sum());
        Console.WriteLine(numbers.Max());
        Console.WriteLine(string.Join(",", numbers.ToArray()));
        Console.WriteLine(numbers.Where(n => n > 1).Count());
        // `TKey` appears only in what the lambda returns, so the lambda has
        // to be bound before the overload can be settled.
        Console.WriteLine(string.Join(",", numbers.OrderBy(n => n).ToArray()));
        Console.WriteLine(string.Join(",", numbers.Select(n => n * 10).ToArray()));
    }
}
"#,
        "3\n3\n2\n6\n3\n3,1,2\n2\n1,2,3\n30,10,20\n",
    );
}

#[test]
fn a_tuple_against_the_real_framework() {
    check(
        "RefTuple",
        r#"
using System;

class RefTuple
{
    static (int, string) Make() { return (1, "two"); }

    static (int count, string name) Named() { return (count: 3, name: "three"); }

    static void Main()
    {
        (int, string) pair = Make();
        Console.WriteLine(pair.Item1);
        Console.WriteLine(pair.Item2);

        // The names are the language's alone: the runtime holds two fields,
        // and a name is another way of saying which one.
        var named = Named();
        Console.WriteLine(named.count);
        Console.WriteLine(named.name);
        Console.WriteLine(named.Item1);
    }
}
"#,
        "1\ntwo\n3\nthree\n3\n",
    );
}

#[test]
fn a_lock_against_the_real_framework() {
    check(
        "RefLock",
        r#"
using System;

class RefLock
{
    static readonly object Gate = new object();
    static int _count;

    static void Bump()
    {
        // A `try`/`finally` around `Monitor.Enter` and `Monitor.Exit`, with
        // the object held in a local so the same one is unlocked.
        lock (Gate)
        {
            _count = _count + 1;
        }
    }

    static void Main()
    {
        Bump();
        Bump();
        Console.WriteLine(_count);

        try
        {
            lock (Gate) { throw new Exception("inside"); }
        }
        catch (Exception e)
        {
            Console.WriteLine(e.Message);
        }
        // Still unlocked, so this goes through.
        Bump();
        Console.WriteLine(_count);
    }
}
"#,
        "2\ninside\n3\n",
    );
}

#[test]
fn a_pattern_on_a_nullable_against_the_real_framework() {
    check(
        "RefNullable",
        r#"
using System;

struct Held
{
    public int Width;
}

class RefNullable
{
    static Held? Make(bool some)
    {
        if (!some) { return null; }
        Held held = new Held();
        held.Width = 4;
        return held;
    }

    static string Describe(Held? value)
    {
        // `{ }` on a `T?` matches the `T`: what the members are read off is
        // the value, not the nullable around it.
        if (value is { Width: > 2 } wide) { return "wide " + wide.Width; }
        if (value is { }) { return "narrow"; }
        return "none";
    }

    static void Main()
    {
        Console.WriteLine(Describe(Make(true)));
        Console.WriteLine(Describe(Make(false)));
        Held small = new Held();
        small.Width = 1;
        Console.WriteLine(Describe(small));
    }
}
"#,
        "wide 4\nnone\nnarrow\n",
    );
}

#[test]
fn a_coalescing_assignment_against_the_real_framework() {
    check(
        "RefCoalesce",
        r#"
using System;

class Cell
{
    public string Name;
    public int? Count;

    public int Reads;
    private string _held;
    public string Held { get { Reads = Reads + 1; return _held; } set { _held = value; } }
}

class RefCoalesce
{
    static void Main()
    {
        Cell cell = new Cell();
        // Only where it is null, and the place is read once.
        cell.Name ??= "first";
        cell.Name ??= "second";
        Console.WriteLine(cell.Name);

        cell.Count ??= 3;
        cell.Count ??= 9;
        Console.WriteLine(cell.Count);

        cell.Held ??= "once";
        Console.WriteLine(cell.Held + " " + cell.Reads);

        string local = null;
        // As an expression, it gives back what is there afterwards.
        Console.WriteLine(local ??= "made");
        Console.WriteLine(local ??= "ignored");
    }
}
"#,
        "first\n3\nonce 2\nmade\nmade\n",
    );
}

#[test]
fn taking_a_tuple_apart_against_the_real_framework() {
    check(
        "RefApart",
        r#"
using System;
using System.Collections.Generic;

class RefApart
{
    static void Main()
    {
        (int, string) pair = (1, "one");
        // A tuple element is a field, so this is an assignment apiece.
        var (number, name) = pair;
        Console.WriteLine(number + " " + name);

        int existing = 0;
        (existing, string other) = (7, "seven");
        Console.WriteLine(existing + " " + other);

        List<(int, string)> pairs = new List<(int, string)>();
        pairs.Add((2, "two"));
        pairs.Add((3, "three"));
        foreach (var (count, word) in pairs)
        {
            Console.WriteLine(count + " " + word);
        }

        // A discard still has a slot; nobody can read it back.
        var (kept, _) = pair;
        Console.WriteLine(kept);
    }
}
"#,
        "1 one\n7 seven\n2 two\n3 three\n1\n",
    );
}

#[test]
fn a_collection_expression_against_the_real_framework() {
    check(
        "RefCollection",
        r#"
using System;
using System.Collections.Generic;

class RefCollection
{
    static int[] Numbers() { return [1, 2, 3]; }

    static List<string> Words() { return ["one", "two"]; }

    static int[] None() { return []; }

    static void Main()
    {
        int[] numbers = Numbers();
        Console.WriteLine(numbers.Length + " " + numbers[0] + numbers[1] + numbers[2]);

        List<string> words = Words();
        Console.WriteLine(words.Count + " " + words[0] + " " + words[1]);

        Console.WriteLine(None().Length);

        // Straight into a variable, with the type written on the left.
        List<int> held = [4, 5];
        Console.WriteLine(held[0] + held[1]);
    }
}
"#,
        "3 123\n2 one two\n0\n9\n",
    );
}

#[test]
fn a_lambda_anywhere_in_a_type_against_the_real_framework() {
    check(
        "RefLambdaPlaces",
        r#"
using System;

class RefLambdaPlaces
{
    // A lambda in a field initializer: the field is the body it belongs to,
    // not the constructor the initializer ends up running in.
    private static Func<int, int> Twice = x => x * 2;
    private Func<int, int> Thrice = x => x * 3;

    // And one in a property's body.
    private int Seed => 4;
    public Func<int, int> Plus => x => x + Seed;

    static int Inner(int n)
    {
        // A lambda inside a local function, capturing the local function's
        // own parameter: the display class belongs to the local function.
        int Helper(int k)
        {
            Func<int, int> add = x => x + k;
            return add(1);
        }
        return Helper(n);
    }

    static void Main()
    {
        RefLambdaPlaces it = new RefLambdaPlaces();
        Console.WriteLine(Twice(5));
        Console.WriteLine(it.Thrice(5));
        Console.WriteLine(it.Plus(5));
        Console.WriteLine(Inner(6));
    }
}
"#,
        "10\n15\n9\n7\n",
    );
}

#[test]
fn a_static_lambda_and_a_tuple_case_label_against_the_real_framework() {
    check(
        "RefStaticLambda",
        r#"
using System;

class RefStaticLambda
{
    static string Pair(int left, int right)
    {
        // `(a, b)` after `case` is a positional pattern: no tuple is a
        // constant, whatever the label would read as on its own.
        switch (left, right)
        {
            case (1, _): return "one";
            case (_, 2): return "two";
            default: return "?";
        }
    }

    static void Main()
    {
        int value = 5;
        // A `static` lambda captures nothing, so nothing around it is in
        // scope and a name it declares is its own.
        Func<int, int> twice = static value => value * 2;
        Console.WriteLine(twice(3));
        Console.WriteLine(value);
        Console.WriteLine(Pair(1, 9));
        Console.WriteLine(Pair(9, 2));
        Console.WriteLine(Pair(9, 9));
    }
}
"#,
        "6\n5\none\ntwo\n?\n",
    );
}

#[test]
fn variance_and_array_covariance_against_the_real_framework() {
    check(
        "RefVariance",
        r#"
using System;
using System.Collections.Generic;

interface ISource<out T> { T Get(); }
interface ISink<in T> { string Put(T value); }

class Source : ISource<string> { public string Get() { return "s"; } }
class Sink : ISink<object> { public string Put(object value) { return "p" + value; } }

class RefVariance
{
    static string Read(ISource<object> source) { return (string)source.Get(); }
    static string Write(ISink<string> sink) { return sink.Put("x"); }
    static int Count(IEnumerable<object> values)
    {
        int n = 0;
        foreach (object value in values) { n++; }
        return n;
    }
    static string First(object[] values) { return (string)values[0]; }

    static void Main()
    {
        // `out T` widens, `in T` narrows, and an array of a reference type
        // converts along with its element type.
        Console.WriteLine(Read(new Source()));
        Console.WriteLine(Write(new Sink()));
        Console.WriteLine(Count(new List<string> { "a", "b", "c" }));
        Console.WriteLine(First(new string[] { "first" }));
    }
}
"#,
        "s\npx\n3\nfirst\n",
    );
}

#[test]
fn a_fully_qualified_name_reaches_a_nested_namespace() {
    check(
        "RefQualified",
        r#"
using System;

class RefQualified
{
    static void Main()
    {
        // `System.Text` is a namespace inside a namespace: nothing can be
        // read from it, and what follows is looked up *inside* it.
        System.Text.StringBuilder builder = new System.Text.StringBuilder();
        builder.Append("a").Append(1);
        Console.WriteLine(builder.ToString());
        Console.WriteLine(System.IO.Path.GetExtension("x.cs"));

        // And `ImmutableArray` beside `ImmutableArray<T>` are two types with
        // one name: the `<int>` says which.
        Console.WriteLine(System.Collections.Immutable.ImmutableArray<int>.Empty.Length);
    }
}
"#,
        "a1\n.cs\n0\n",
    );
}

#[test]
fn a_collection_expression_through_its_builder() {
    check(
        "RefBuilder",
        r#"
using System;
using System.Collections.Immutable;

class RefBuilder
{
    static void Main()
    {
        // `ImmutableArray<T>` carries `[CollectionBuilder(typeof(ImmutableArray),
        // "Create")]`, and nothing else says how one is made.
        ImmutableArray<int> numbers = [1, 2, 3];
        ImmutableArray<string> names = ["a", "b"];
        ImmutableArray<int> none = [];
        Console.WriteLine(numbers.Length + names.Length + none.Length);
        Console.WriteLine(numbers[2] + names[1]);
    }
}
"#,
        "5\n3b\n",
    );
}

#[test]
fn an_index_and_a_range_against_the_real_framework() {
    check(
        "RefIndexRange",
        r#"
using System;

class RefIndexRange
{
    static void Main()
    {
        int[] numbers = new int[] { 1, 2, 3, 4, 5 };
        // `^k` counts from the end, and the length it counts from is asked
        // for once.
        Console.WriteLine(numbers[^1]);
        Console.WriteLine(numbers[^numbers.Length]);

        int[] middle = numbers[1..4];
        Console.WriteLine(middle.Length + " " + middle[0] + middle[2]);

        string text = "abcdef";
        Console.WriteLine(text[^2]);
        Console.WriteLine(text[1..3]);
        Console.WriteLine(text[..^4]);

        // And as values of their own.
        Index last = ^1;
        Range all = ..;
        Console.WriteLine(numbers[last] + " " + numbers[all].Length);
    }
}
"#,
        "5\n1\n3 24\ne\nbc\nab\n5 5\n",
    );
}

#[test]
fn a_lambda_in_an_accessor_block_against_the_real_framework() {
    check(
        "RefAccessorLambda",
        r#"
using System;
using System.Collections.Generic;
using System.Linq;

class RefAccessorLambda
{
    private List<int> _values = new List<int> { 1, 2, 3 };
    private int _seen;

    // `=> e` is one body under the property; `{ get { ... } }` is one body
    // per accessor, and what is written in it belongs to the accessor.
    public int Arrow => _values.Select(v => v + 1).First();
    public int Block { get { return _values.Select(v => v + 2).First(); } }
    public int Seen { set { _seen = _values.Select(v => v + value).First(); } }
    public int this[int at] { get { return _values.Select(v => v + at).First(); } }

    static void Main()
    {
        RefAccessorLambda it = new RefAccessorLambda();
        it.Seen = 10;
        Console.WriteLine(it.Arrow + " " + it.Block + " " + it._seen + " " + it[100]);
    }
}
"#,
        "2 3 11 101\n",
    );
}

#[test]
fn a_constant_of_a_referenced_assembly_is_the_value_against_the_real_framework() {
    check(
        "RefConstants",
        r#"
using System;
class RefConstants
{
    static void Main()
    {
        // A literal field has no storage: loading one looks for a field that
        // is not there, and the value has to come out of the metadata.
        Console.WriteLine((int)char.MaxValue);
        Console.WriteLine(int.MaxValue);
        Console.WriteLine(long.MinValue);
        Console.WriteLine(double.NaN);
    }
}
"#,
        "65535\n2147483647\n-9223372036854775808\nNaN\n",
    );
}

#[test]
fn a_conditional_call_is_written_out_against_the_real_framework() {
    check(
        "RefConditional",
        r#"
using System;
using System.Diagnostics;

class RefConditional
{
    static int _calls;
    static bool Count() { _calls = _calls + 1; return false; }

    [Conditional("VERBOSE")]
    static void Note(string text) { Console.WriteLine("note " + text); }

    static void Main()
    {
        // `DEBUG` is not defined here, so the call goes and so does
        // everything that would have been evaluated for it — including the
        // assertion that would otherwise have failed.
        Debug.Assert(Count(), "never evaluated");
        Note("gone");
        Console.WriteLine(_calls);
    }
}
"#,
        "0\n",
    );
}

#[test]
fn null_given_to_a_nullable_is_the_empty_one_against_the_real_framework() {
    check(
        "RefEmptyNullable",
        r#"
using System;

struct Pair
{
    public int A;
    public Pair(int a) { A = a; }
}

class RefEmptyNullable
{
    // `null` here is not a reference: a `Pair?` is a struct, and loading a
    // null where one is wanted is not a program at all.
    static Pair? Pick(bool empty) { return empty ? null : new Pair(7); }
    static int? Number(bool empty) { return empty ? null : 5; }

    static void Main()
    {
        Console.WriteLine(Pick(true) == null);
        Console.WriteLine(Pick(false).Value.A);
        Console.WriteLine(Number(true) == null);
        Console.WriteLine(Number(false).Value);
        int? given = null;
        Console.WriteLine(given.HasValue);
    }
}
"#,
        "True\n7\nTrue\n5\nFalse\n",
    );
}

#[test]
fn an_array_has_the_members_system_array_declares() {
    check(
        "RefArrayMembers",
        r#"
using System;

class RefArrayMembers
{
    static void Main()
    {
        int[,] table = new int[3, 4];
        // Nothing declares `int[,]`, so `GetLength` and `Rank` can only come
        // from `System.Array`, which every array type derives from.
        Console.WriteLine(table.GetLength(1));
        Console.WriteLine(table.Rank);
        Console.WriteLine(table.LongLength);
    }
}
"#,
        "4\n2\n12\n",
    );
}

#[test]
fn a_reference_to_a_ref_readonly_member_carries_the_modifier_it_was_declared_with() {
    check(
        "RefReadonlySpan",
        r#"
using System;

class RefReadonlySpan
{
    static void Main()
    {
        // `ReadOnlySpan<T>.this[int]` gives back `ref readonly T`, which
        // metadata spells `!0&` under a `modreq` naming `InAttribute`. A
        // reference that leaves the modifier out finds no such method.
        ReadOnlySpan<char> span = "abc".AsSpan();
        Console.WriteLine(span[1]);
        Console.WriteLine(span.Length);
    }
}
"#,
        "b\n3\n",
    );
}

#[test]
fn a_lambda_reaches_only_the_overload_that_wants_a_delegate() {
    check(
        "RefLambdaOverload",
        r#"
using System;

class RefLambdaOverload
{
    static void Main()
    {
        // `Lazy<int>` also takes a `bool`, and a lambda is applicable to
        // neither it nor anything else that is not a delegate (§12.6.4.4).
        Lazy<int> once = new Lazy<int>(() => 3);
        Console.WriteLine(once.Value);
        Console.WriteLine(new Lazy<string>(() => "later").Value);
    }
}
"#,
        "3\nlater\n",
    );
}

#[test]
fn a_lambda_or_a_method_group_has_a_delegate_type_of_its_own() {
    // `object`, `Delegate` and `var` take the type a lambda or a method group
    // has on its own (C# 10): an `Action` or a `Func` where one fits, and a
    // delegate type the compiler declares where a `ref` parameter, a default
    // value or `params` needs one.
    check(
        "NaturalDelegates",
        r#"
using System;

class NaturalDelegates
{
    static void Main()
    {
        object o = () => { };
        Delegate d = Main;
        var f = (int x) => x + 1;
        Report(o);
        Report(d);
        Report(f);
        Report((ref int x, int y) => { });
        Report((int x, out int y) => y = x);
        var g = (int x = 10, params int[] rest) => x + rest.Length;
        Report(g);
        Console.WriteLine(g());
        Console.WriteLine(g(1, 2, 3));
        var h = Twice;
        Console.WriteLine(h(3));
        Report(Twice);
    }
    static int Twice(int x = 2) => x * 2;
    static void Report(object d) => Console.WriteLine(d.GetType());
}
"#,
        "System.Action\nSystem.Action\nSystem.Func`2[System.Int32,System.Int32]\n\
<>A{00000001}`2[System.Int32,System.Int32]\n\
<>F{00000010}`3[System.Int32,System.Int32,System.Int32]\n\
<>f__AnonymousDelegate0`3[System.Int32,System.Int32,System.Int32]\n10\n3\n6\n\
<>f__AnonymousDelegate1`2[System.Int32,System.Int32]\n",
    );
}

#[test]
fn natural_types_settle_arrays_type_arguments_and_overloads() {
    // An array of lambdas and method groups is of their best common type; a
    // bare `T` is inferred from a lambda's natural type; a method group that
    // returns the wrong thing for a delegate leaves only `Delegate`; and a
    // lambda may state a `ref` return type.
    check(
        "NaturalInference",
        r#"
using System;

class NaturalInference
{
    static int i = 7;
    static int M1(string s) => s.Length;
    static T F<T>(T x, T y) => y;
    static void FA(Delegate d) => Console.WriteLine("FA(Delegate)");
    static void FA(Action d) => Console.WriteLine("FA(Action)");
    static void F1() { }
    static int F2() => 0;
    static void Main()
    {
        var a = new[] { M1, (string s) => int.Parse(s) };
        Console.WriteLine(a.GetType());
        Console.WriteLine(F(() => string.Empty, () => new object()).GetType());
        FA(F1);
        FA(F2);
        var r = ref int () => ref i;
        r() = 8;
        Console.WriteLine(i);
        var e = () => () => 1;
        Console.WriteLine(e().GetType());
        var b = (bool flag) => { if (flag) return "s"; return new object(); };
        Console.WriteLine(b.GetType());
    }
}
"#,
        "System.Func`2[System.String,System.Int32][]\nSystem.Func`1[System.Object]\n\
FA(Action)\nFA(Delegate)\n8\nSystem.Func`1[System.Int32]\n\
System.Func`2[System.Boolean,System.Object]\n",
    );
}

#[test]
fn lambdas_and_method_groups_pick_their_overloads_by_shape() {
    // A `ref` return, an `in` parameter and a more specific parameter type
    // each decide which delegate a lambda or a group becomes; a nested
    // `async` lambda matches exactly only through its own result; a lambda
    // reaches a user-defined conversion; and `delegate { }` takes anything.
    check(
        "LambdaShapes",
        r#"
using System;
using System.Threading.Tasks;

class Base { public static Base Instance = new Base(); }
class Derived : Base { }
class C
{
    public string Text = "";
    public static explicit operator C(Func<string> f) => new C { Text = f() };
}
class LambdaShapes
{
    delegate ref T RefFunc<A, T>(A a);
    static void Test(RefFunc<Derived, Base> f) => Console.WriteLine("ref");
    static void Test(Func<Derived, Base> f) => Console.WriteLine("value");
    static void F(in DateTime x) => Console.WriteLine("in");
    static void F(DateTime x) => Console.WriteLine("value");
    static string M(Base b) => "base";
    static string M(Derived d) => "derived";
    static void Goo(Func<Func<Task<short>>> x) => Console.WriteLine("short");
    static void Goo(Func<Func<Task<int>>> x) => Console.WriteLine("int");
    static void Main()
    {
        Test(t => Base.Instance);
        Test(t => ref Base.Instance);
        Action<DateTime> a = F;
        a(DateTime.MaxValue);
        Func<Derived, string> m = M;
        Console.WriteLine(m(null));
        Goo(() => async () => 0);
        Console.WriteLine(((C)(() => "cast")).Text);
        Func<int, int> any = delegate { return 9; };
        Console.WriteLine(any(1));
    }
}
"#,
        "value\nref\nvalue\nderived\nint\ncast\n9\n",
    );
}

#[test]
fn a_lambda_reaches_base_and_constructor_parameters_and_open_types() {
    // `base.F()` in a lambda makes it an instance method; a lambda handed
    // to a constructor initializer finds its captures made before the call,
    // `this` joining them after; and `typeof(Outer<>)` in a generic closure
    // is the definition, not a construction.
    check(
        "LambdaReach",
        r#"
using System;

class B { public virtual string F() => "base"; }
class LambdaReach : B
{
    int x;
    public override string F() => "derived";
    LambdaReach(int x) : this(z => x + z)
    {
        this.x = x + 100;
        Func<int, int> g = z => z + x + this.x;
        Console.WriteLine(g(1000));
    }
    LambdaReach(Func<int, int> f) { Console.WriteLine(f(10)); }
    LambdaReach() { }
    void Run()
    {
        Func<string> f = () => base.F();
        Console.WriteLine(f());
    }
    class Outer<T>
    {
        public Func<string> Get(T value) => () => typeof(Outer<>).Name + typeof(Outer<T>).Name + value;
    }
    static void Main()
    {
        new LambdaReach(1);
        new LambdaReach().Run();
        Console.WriteLine(new Outer<int>().Get(5)());
    }
}
"#,
        "11\n1102\nbase\nOuter`1Outer`15\n",
    );
}

#[test]
fn two_discard_parameters_leave_the_name_to_what_is_outside() {
    check(
        "LambdaDiscards",
        r#"
class C(int _)
{
    public System.Func<int, int> One() => (_) => _;
    public System.Func<int, int, int> Two() => (_, _) => _;
}
class LambdaDiscards
{
    static void Main()
    {
        var c = new C(20);
        System.Console.WriteLine(c.One()(-1));
        System.Console.WriteLine(c.Two()(-2, -3));
    }
}
"#,
        "-1\n20\n",
    );
}

#[test]
fn an_optional_attribute_makes_a_parameter_optional() {
    // `[Optional, DefaultParameterValue(v)]` is `= v` written as attributes,
    // on a method, a method group's natural type and a lambda alike; and a
    // `decimal` default is a `decimal`, not an integer zero.
    check(
        "OptionalAttributes",
        r#"
using System;
using System.Runtime.InteropServices;

class OptionalAttributes
{
    static string Named([Optional][DefaultParameterValue(nameof(Named))] string x) => x;
    static decimal Zero([Optional] decimal d) => d;
    static decimal? Five(decimal? d = 5) => d;
    static void Main()
    {
        Console.WriteLine(Named());
        var named = Named;
        Console.WriteLine(named());
        var lam = ([Optional, DefaultParameterValue(3)] int x) => x;
        Console.WriteLine(lam());
        Console.WriteLine(Zero());
        Console.WriteLine(Five());
    }
}
"#,
        "Named\nNamed\n3\n0\n5\n",
    );
}

#[test]
fn an_anonymous_type_hashes_and_names_its_fields_as_roslyn_does() {
    check(
        "AnonymousShapes",
        r#"
using System;
using System.Reflection;

class AnonymousShapes
{
    static void Main()
    {
        var empty = new { };
        Console.WriteLine(empty);
        Console.WriteLine(empty.GetHashCode());
        var ab = new { a = 1, b = 2 };
        var ba = new { b = 1, a = 2 };
        Console.WriteLine(ab.GetHashCode() == ba.GetHashCode());
        foreach (var field in ab.GetType().GetFields(BindingFlags.Instance | BindingFlags.NonPublic))
            Console.WriteLine(field.Name + " " + field.Attributes);
    }
}
"#,
        "{ }\n0\nFalse\n<a>i__Field Private, InitOnly\n<b>i__Field Private, InitOnly\n",
    );
}

#[test]
fn a_decimal_literal_is_the_number_its_parts_make() {
    check(
        "RefDecimal",
        r#"
using System;

class RefDecimal
{
    static void Main()
    {
        decimal half = 1.5m;
        decimal small = 0.0001m;
        decimal big = 123456789012345678901234567m;
        Console.WriteLine(half);
        Console.WriteLine(small);
        Console.WriteLine(big);
        Console.WriteLine(half + half);
    }
}
"#,
        "1.5\n0.0001\n123456789012345678901234567\n3.0\n",
    );
}

#[test]
fn a_collection_expression_may_spread_what_it_cannot_count() {
    check(
        "RefSpread",
        r#"
using System;
using System.Collections.Generic;
using System.Collections.Immutable;

class RefSpread
{
    static void Main()
    {
        int[] head = [1, 2];
        List<int> tail = [4, 5];
        // How many `..rest` adds is not known until it is walked, so the
        // elements go into a list and the array is what it turns out to hold.
        int[] joined = [..head, 3, ..tail];
        Console.WriteLine(joined.Length);
        Console.WriteLine(joined[2]);
        Console.WriteLine(joined[4]);
        ImmutableArray<int> built = [..joined, 6];
        Console.WriteLine(built.Length);
        Console.WriteLine(built[5]);
    }
}
"#,
        "5\n3\n5\n6\n6\n",
    );
}

#[test]
fn an_enum_reaches_the_members_system_enum_declares() {
    check(
        "RefEnumBase",
        r#"
using System;

[Flags]
enum Marks { None = 0, First = 1, Second = 2 }

class RefEnumBase
{
    static void Main()
    {
        Marks marks = Marks.First | Marks.Second;
        // `HasFlag` is declared on `System.Enum`, which is a class: the value
        // reaches it boxed, and so does the argument.
        Console.WriteLine(marks.HasFlag(Marks.First));
        Console.WriteLine(marks.HasFlag(Marks.None));
        Enum widened = marks;
        Console.WriteLine(widened.Equals(marks));
    }
}
"#,
        "True\nTrue\nTrue\n",
    );
}

#[test]
fn a_query_is_the_calls_it_is_shorthand_for() {
    check(
        "RefQuerying",
        r#"
using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;

class Program
{
    static void Main()
    {
        int[] values = new int[] { 3, 1, 4, 1, 5 };
        // `where` and `select` are `Where` and `Select`, found the way the
        // source would find them: as extension methods on `IEnumerable<T>`.
        IEnumerable<string> shown =
            from n in values
            where n > 1
            orderby n descending
            select "n" + n;
        foreach (string s in shown) { Console.WriteLine(s); }

        // `from int n in xs` reads each element as that type, which is a cast.
        ArrayList mixed = new ArrayList();
        mixed.Add(7);
        mixed.Add(8);
        IEnumerable<int> read = from int n in mixed where n > 7 select n;
        foreach (int n in read) { Console.WriteLine(n); }
    }
}
"#,
        "n5\nn4\nn3\n8\n",
    );
}

#[test]
fn a_captured_value_type_is_reached_through_the_field_it_lives_in() {
    check(
        "RefCapturedStruct",
        r#"
using System;
using System.Collections.Immutable;
using System.Linq;

class State
{
    public bool Ok;
    public int First;

    internal State(ImmutableArray<int> values)
    {
        // `values` is a struct that now lives in a field of the display
        // class, and a call on it needs the address of that field.
        Func<int> first = () => values[0];
        First = first();
        Ok = values.All(value => value >= values[0]);
    }
}

class Program
{
    static void Main()
    {
        State state = new State(ImmutableArray.Create(5, 6));
        Console.WriteLine(state.First);
        Console.WriteLine(state.Ok);
    }
}
"#,
        "5\nTrue\n",
    );
}

/// Nothing in a type's flags says `ref struct`: the runtime reads
/// `IsByRefLikeAttribute`, and without it refuses a type that holds a span.
#[test]
fn a_ref_struct_says_so_in_metadata_and_may_hold_a_span() {
    check(
        "RefStruct",
        r#"
using System;

ref struct Reader
{
    private ReadOnlySpan<char> rest;

    public Reader(ReadOnlySpan<char> span) { rest = span; }

    public int Left() { return rest.Length; }

    public override string ToString() { return rest.ToString(); }
}

class Program
{
    static void Main()
    {
        Reader reader = new Reader("abc".AsSpan());
        Console.WriteLine(reader.Left());
        Console.WriteLine(reader.ToString());
    }
}
"#,
        "3\nabc\n",
    );
}

/// An overload taking something that is not a delegate cannot be the one a
/// lambda was written for, and a lambda inside a generic type is a method of
/// a construction of it.
#[test]
fn a_lambda_picks_the_overload_that_takes_one_and_carries_the_type_it_sits_in() {
    check(
        "RefLambdaOverloadTwo",
        r#"
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;

namespace Held
{
    internal static class Extras
    {
        // Same name, same arity, and nothing a lambda can be.
        public static IOrderedEnumerable<T> OrderBy<T>(this IEnumerable<T> source, IComparer<T> comparer)
        {
            return Enumerable.OrderBy(source, t => t, comparer);
        }
    }

    internal sealed class Ordered<T>
    {
        private readonly ImmutableDictionary<T, uint> map;

        public Ordered(ImmutableDictionary<T, uint> map) { this.map = map; }

        public IEnumerable<T> InInsertionOrder
        {
            get { return map.OrderBy(kv => kv.Value).Select(kv => kv.Key); }
        }
    }

    class Program
    {
        static void Main()
        {
            ImmutableDictionary<string, uint> map = ImmutableDictionary.Create<string, uint>()
                .Add("b", 2u).Add("a", 1u);
            foreach (string s in new Ordered<string>(map).InInsertionOrder) { Console.WriteLine(s); }
        }
    }
}
"#,
        "a\nb\n",
    );
}

/// `in` is a `T&` in metadata like `ref` and `out`, and the parameter's own
/// flag is what tells it apart; a `ref` local passed on is the reference it
/// already holds.
#[test]
fn an_in_parameter_read_from_metadata_takes_the_in_that_was_written() {
    check(
        "RefInParameter",
        r#"
using System;
using System.Runtime.CompilerServices;
using System.Threading;

class RefInParameter
{
    static void Main()
    {
        int x = 1;
        ref int slot = ref Unsafe.AsRef(in x);
        slot = 5;
        Console.WriteLine(x);
        int[] held = new int[] { 1 };
        ref int[] where = ref Unsafe.AsRef(in held);
        int[] old = Interlocked.Exchange(ref where, new int[] { 2, 3 });
        Console.WriteLine(old.Length);
        Console.WriteLine(held.Length);
    }
}
"#,
        "5\n1\n2\n",
    );
}

/// Seventy-two arguments to one `params T[]`: what `T` is comes from all of
/// them, and zipping them against the parameters stops at the first.
#[test]
fn a_params_array_says_what_the_type_argument_is() {
    check(
        "RefParamsInference",
        r#"
using System;
using System.Collections.Immutable;

class RefParamsInference
{
    static readonly ImmutableArray<int> Primes = ImmutableArray.Create(3, 7, 11, 17, 23, 29, 37);

    static void Main()
    {
        Console.WriteLine(Primes.Length);
        Console.WriteLine(Primes[6]);
        ImmutableArray<string> names = ImmutableArray.Create("a", "b", "c", "d", "e");
        Console.WriteLine(names[4]);
    }
}
"#,
        "7\n37\ne\n",
    );
}

/// `slot = ref other` gives the local a different reference to hold; it does
/// not write through the one it has.
#[test]
fn a_ref_local_can_be_given_a_different_reference_to_hold() {
    check(
        "RefReassign",
        r#"
using System;
using System.Runtime.CompilerServices;

class RefReassign
{
    static ref int Pick(int[] held, int at) { return ref held[at]; }

    static void Main()
    {
        int[] held = new int[] { 1, 2, 3 };
        ref int slot = ref Unsafe.NullRef<int>();
        slot = ref Pick(held, 1);
        slot = 9;
        Console.WriteLine(held[1]);
        slot = ref Pick(held, 2);
        slot = 7;
        Console.WriteLine(held[2]);
        Console.WriteLine(held[1]);
    }
}
"#,
        "9\n7\n9\n",
    );
}

/// `x?.M()` on a `T?` asks whether it holds anything, and reaches the value
/// inside rather than the `T?` around it.
#[test]
fn a_question_mark_on_a_value_that_can_be_missing_reaches_what_is_inside() {
    check(
        "RefConditionalNullable",
        r#"
using System;
using System.Collections.Generic;
using System.Linq;

class RefConditionalNullable
{
    struct ValueHolder { public int Count; }

    static string Read(List<int> given)
    {
        int? first = given?.FirstOrDefault();
        return first.HasValue ? first.Value.ToString() : "none";
    }

    static int Count(ValueHolder? held) { return held?.Count ?? -1; }

    static void Main()
    {
        Console.WriteLine(Read(new List<int> { 4, 5 }));
        Console.WriteLine(Read(null));
        ValueHolder one = new ValueHolder();
        one.Count = 3;
        Console.WriteLine(Count(one));
        Console.WriteLine(Count(null));
    }
}
"#,
        "4\nnone\n3\n-1\n",
    );
}

/// `where TDerived : TBase` names a type parameter, which no `TypeDef` or
/// `TypeRef` stands for; a local function copying that constraint has to say
/// the same thing, or the runtime refuses what it is given.
#[test]
fn a_constraint_that_names_another_type_parameter_is_carried_to_a_local_function() {
    check(
        "RefConstraintOnParameter",
        r#"
using System;
using System.Collections.Immutable;

class RefConstraintOnParameter
{
    internal static string Make<TBase, TDerived>(TDerived given)
        where TBase : class
        where TDerived : class, TBase
    {
        static ImmutableArray<TBase> up(TDerived one)
        {
            return ImmutableArray<TBase>.CastUp(ImmutableArray.Create(one));
        }
        return up(given).Length.ToString() + "/" + up(given)[0];
    }

    static void Main()
    {
        Console.WriteLine(Make<object, string>("a"));
    }
}
"#,
        "1/a\n",
    );
}

/// §10.2.11: a variance conversion may vary only where both sides are held by
/// reference, and `where TSymbol : Symbol` makes one as surely as `class`
/// does.
#[test]
fn a_variance_conversion_reaches_a_type_parameter_constrained_to_a_class() {
    check(
        "RefVarianceParameter",
        r#"
using System;
using System.Collections.Generic;

class Symbol { }

class Derived : Symbol { }

sealed class Comparer : IEqualityComparer<Symbol>
{
    public static readonly Comparer Everything = new Comparer();

    public bool Equals(Symbol a, Symbol b) { return object.ReferenceEquals(a, b); }

    public int GetHashCode(Symbol s) { return 0; }
}

class Pool<T>
{
    public static Pool<T> Create(IEqualityComparer<T> comparer) { return new Pool<T>(); }
}

static class Holder
{
    private static class Held<TSymbol> where TSymbol : Symbol
    {
        internal static readonly Pool<TSymbol> Instance = Pool<TSymbol>.Create(Comparer.Everything);
    }

    public static string Which<TSymbol>() where TSymbol : Symbol
    {
        return Held<TSymbol>.Instance == null ? "none" : "made";
    }
}

class Program
{
    static void Main() { Console.WriteLine(Holder.Which<Derived>()); }
}
"#,
        "made\n",
    );
}

/// A base that is a construction of a framework type is chained to through
/// that construction: the open definition's constructor is not a method the
/// runtime can call.
#[test]
fn a_constructed_framework_base_is_chained_to_through_its_construction() {
    check(
        "RefConstructedBase",
        r#"
using System;
using System.Collections.Generic;

class Symbol { public int Id; }

sealed class Same : EqualityComparer<Symbol>
{
    public static readonly EqualityComparer<Symbol> Only = new Same();

    public override bool Equals(Symbol a, Symbol b) { return a.Id == b.Id; }

    public override int GetHashCode(Symbol s) { return s.Id; }
}

class RefConstructedBase
{
    static void Main()
    {
        Symbol a = new Symbol();
        a.Id = 1;
        Symbol b = new Symbol();
        b.Id = 1;
        Console.WriteLine(Same.Only.Equals(a, b));
        Console.WriteLine(Same.Only.GetHashCode(a));
    }
}
"#,
        "True\n1\n",
    );
}

#[test]
fn what_a_primary_constructor_an_event_and_a_lifted_equality_run_as() {
    check(
        "RefPrimaryEvents",
        r#"
using System;
using System.Collections.Generic;
using System.Linq;

readonly record struct DebugId(int Ordinal, int Generation);
record struct Info(int Offset, DebugId Id) { public string Show() => $"{Id.Ordinal}@{Offset}"; }
abstract class Node(int depth) { public int Depth { get; } = depth; }
abstract class BinaryNode(Node left, Node right) : Node(1 + Math.Max(left.Depth, right.Depth))
{
    public Node Left { get; } = left;
    public Node Right { get; } = right;
}
sealed class Leaf() : Node(0) { }
sealed class AndNode(Node left, Node right) : BinaryNode(left, right) { }
struct Disposer<T>(T instance, string tag) where T : class
{
    public string Free() => instance is null ? "nothing " + tag : "freed " + tag;
}
struct Span { public int Start; public static bool operator ==(Span a, Span b) => a.Start == b.Start; public static bool operator !=(Span a, Span b) => a.Start != b.Start; public override bool Equals(object o) => false; public override int GetHashCode() => 0; }
abstract class Tests { public sealed class Not : Tests { } public sealed class One : Tests { } }

class Program
{
    public event EventHandler<string>? Failed;
    readonly HashSet<string> _set = new() { "b", "c" };
    static bool AreEqual(string a, string b) => a == b;

    void Raise(string message) => Failed?.Invoke(this, message);
    static void OnFailed(object? sender, string message) => Console.WriteLine("failed: " + message);

    static string Which(Tests t)
    {
        switch (t)
        {
            case Tests.Not: return "not";
            case Tests.One: return "one";
        }
        return "?";
    }

    static void Main()
    {
        var and = new AndNode(new Leaf(), new AndNode(new Leaf(), new Leaf()));
        Console.WriteLine(and.Depth);
        Console.WriteLine(new Info(3, new DebugId(7, 1)).Show());
        Console.WriteLine(new Disposer<string>("x", "one").Free());
        Console.WriteLine(new Disposer<string>(null, "two").Free());

        var program = new Program();
        program.Raise("dropped");
        program.Failed += OnFailed;
        program.Raise("seen");
        program.Failed -= OnFailed;
        program.Raise("dropped again");

        Span? a = new Span { Start = 1 };
        Span? b = null;
        Span c = new Span { Start = 1 };
        Console.WriteLine(a == b);
        Console.WriteLine(a != b);
        Console.WriteLine(a == c);
        Console.WriteLine(b == null);
        DebugId? id = new DebugId(1, 2);
        Console.WriteLine(id == new DebugId(1, 2));

        Console.WriteLine(Which(new Tests.Not()) + Which(new Tests.One()));
        List<string>? none = null;
        var some = new List<string> { "p", "q" };
        Console.WriteLine(none?[0] ?? "none");
        Console.WriteLine(some?[1]?.ToUpper());
        some[^1] = "z";
        var array = new[] { 1, 2, 3 };
        array[^1] = 9;
        Console.WriteLine(string.Join(",", some) + " " + string.Join(",", array));

        var words = new[] { "a", "b", "c" };
        Console.WriteLine(string.Join(",", words.Where(program._set.Contains)));
        var pairs = new[] { "x", "y" };
        Console.WriteLine(pairs.SequenceEqual(new[] { "x", "y" }, EqualityComparer<string>.Default) && Enumerable.Zip(pairs, pairs, AreEqual).All(same => same));
        Func<string, string, bool> refs = ReferenceEquals;
        Console.WriteLine(refs("a", "a"));
        var keys = new List<int> { 3, 1, 2 };
        keys.Sort(Comparer<int>.Default.Compare);
        Console.WriteLine(string.Join(",", keys));
        Func<int, int> inc = static int (n) => n + 1;
        Console.WriteLine(inc(41));
    }
}
"#,
        "2\n7@3\nfreed one\nnothing two\nfailed: seen\nFalse\nTrue\nTrue\nTrue\nTrue\nnotone\nnone\nQ\np,z 1,2,9\nb,c\nTrue\nTrue\n1,2,3\n42\n",
    );
}

#[test]
fn the_shapes_a_second_corpus_sweep_turned_up() {
    check(
        "RefSecondSweep",
        r#"
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Globalization;
using System.Linq;

struct Pooled : IDisposable { public static int Freed; void IDisposable.Dispose() { Freed++; } }
sealed class Blob : IDisposable { public static int Freed; void IDisposable.Dispose() { Freed++; } }
delegate int Skipper<T>(List<T> list, T sentinel);
class Walker { public int Depth; protected Walker(int depth = 3) { Depth = depth; } }
class Finder : Walker { }
class Finder<T> : Walker { public T? Item; }
class Holder<T> { public static Holder<T> Default { get; } = new Holder<T>(); public IEnumerable<int> Items { get { yield return 1; yield return 2; } } }
static class Marshal
{
    public static string List(string node) => "one:" + node;
    public static string List(string[] nodes) => "many:" + nodes.Length;
}

class Program
{
    static int Skip<T>(List<T> list, T sentinel) => list.IndexOf(sentinel);
    static int Run<T>(Skipper<T> skipper, List<T> list, T value) => skipper(list, value);
    static ImmutableArray<int> Sides(List<int>? stores) => stores is null ? [] : stores.ToImmutableArray();
    static (int Count, ImmutableArray<string> Names) Pair(string? p) => (1, p is { } q ? [q] : []);
    static IEnumerable<string> Members(Dictionary<string, ImmutableArray<string>>? map, string key)
    {
        foreach (var member in map != null && map.TryGetValue(key, out var found) ? found : [])
            yield return member;
    }
    static int Decon((int a, int b)? pair, (int, int) other) => pair is var (x, y) ? x + y : other is var (p, q) ? p - q : 0;

    static void Main()
    {
        CultureInfo.CurrentCulture = CultureInfo.InvariantCulture;
        Console.WriteLine(Run(Skip, new List<int> { 1, 2 }, 2));
        Console.WriteLine($"{255:X4}|{3.14159,8:N2}|{"ab",-4}|");
        Console.WriteLine(FormattableString.Invariant($"{1.5:F3}"));
        ImmutableArray<int> a = [1, 2];
        ImmutableArray<int>? b = null;
        Console.WriteLine(a == b);
        Console.WriteLine(a != null);
        Console.WriteLine(Sides(null).Length + Sides(new List<int> { 4, 5, 6 }).Length);
        Console.WriteLine(Pair("z").Names.Length + Pair(null).Names.Length);
        var map = new Dictionary<string, ImmutableArray<string>> { ["k"] = ["m", "n"] };
        Console.WriteLine(string.Join(",", Members(map, "k")) + "|" + string.Join(",", Members(map, "x")) + "|" + string.Join(",", Members(null, "k")));
        Console.WriteLine(Marshal.List(["q"]) + " " + Marshal.List("q"));
        var counts = new Dictionary<string, int> { ["a"] = 1 };
        Console.WriteLine(counts.TryGetValue("a", out var _) + " " + counts.TryGetValue("b", out int _));
        Console.WriteLine(Decon((2, 3), (0, 0)) + " " + Decon(null, (9, 4)));
        using (var p = new Pooled()) { }
        using (var blob = new Blob()) { }
        Console.WriteLine(Pooled.Freed + Blob.Freed);
        Console.WriteLine(new Finder().Depth + new Finder<string>().Depth);
        Console.WriteLine(Holder<string>.Default.Items.Sum() + Holder<int>.Default.Items.Count());
    }
}
"#,
        "1\n00FF|    3.14|ab  |\n1.500\nFalse\nTrue\n3\n1\nm,n||\nmany:1 one:q\nTrue False\n5 5\n2\n6\n5\n",
    );
}

#[test]
fn an_async_method_runs_as_a_state_machine() {
    check(
        "RefAsync",
        r#"
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Threading;
using System.Threading.Tasks;

class Box<T>
{
    public T Value;
    public Box(T value) { Value = value; }
    public async Task<T> Twice(Func<T, Task<T>> step)
    {
        var once = await step(Value).ConfigureAwait(false);
        return await step(once).ConfigureAwait(false);
    }
}

static class Program
{
    static int s_log;
    static Task<int> Double(int x) => Task.FromResult(x * 2);
    static Task<int> Length(string s) => Task.FromResult(s.Length);

    static async Task<int> Compute(int n)
    {
        await Task.Yield();
        int total = 0;
        for (int i = 0; i < n; i++)
        {
            total += await Task.FromResult(i).ConfigureAwait(false);
        }
        return total;
    }

    static async Task Log(string message)
    {
        await Task.Delay(1);
        s_log++;
        Console.WriteLine(message);
    }

    static async ValueTask<string> Guarded(bool fail)
    {
        try
        {
            await Task.Delay(1).ConfigureAwait(false);
            if (fail) throw new InvalidOperationException("boom");
            return "fine";
        }
        catch (InvalidOperationException e)
        {
            return "caught " + e.Message;
        }
        finally
        {
            s_log++;
        }
    }

    static async Task<ImmutableArray<int>> Gather<T>(IEnumerable<T> items, Func<T, Task<int>> map)
    {
        var builder = ImmutableArray.CreateBuilder<int>();
        foreach (var item in items)
        {
            builder.Add(await map(item).ConfigureAwait(false));
        }
        return builder.ToImmutable();
    }

    static async Task<(int, string)> Pair() => (await Compute(3), await Guarded(false));

    static async Task<string> Failing()
    {
        await Task.Delay(1);
        throw new ArgumentException("late");
    }

    static void Main() => Run().GetAwaiter().GetResult();

    static async Task Run()
    {
        Console.WriteLine(await Compute(4));
        await Log("logged");
        Console.WriteLine(await Guarded(false));
        Console.WriteLine(await Guarded(true));
        Console.WriteLine(await new Box<int>(5).Twice(Double));
        var gathered = await Gather(new[] { "a", "bb", "ccc" }, Length);
        Console.WriteLine(string.Join(",", gathered));
        var (n, s) = await Pair();
        Console.WriteLine(n + " " + s);
        try
        {
            await Failing();
        }
        catch (ArgumentException e)
        {
            Console.WriteLine("failed: " + e.Message);
        }
        Console.WriteLine(s_log);
    }
}
"#,
        "6\nlogged\nfine\ncaught boom\n20\n1,2,3\n3 fine\nfailed: late\n4\n",
    );
}

/// A machine's `try` with both catches and a `finally` is two regions that
/// start at one instruction; the dispatch into them lands on a `nop` before
/// them, as `csc` writes it, since the JIT crashes on a branch to that start.
#[test]
fn a_machine_resumes_inside_a_try_with_catches_and_a_finally() {
    check(
        "RefAsyncTryCatchFinally",
        r#"
using System;
using System.Threading.Tasks;

static class Program
{
    static int s_log;

    static async Task<string> Guarded(bool fail)
    {
        try
        {
            await Task.CompletedTask;
            await Task.Yield();
            if (fail) throw new InvalidOperationException("boom");
            return "fine";
        }
        catch (InvalidOperationException e)
        {
            return "caught " + e.Message;
        }
        finally
        {
            s_log++;
        }
    }

    static async Task Run()
    {
        Console.WriteLine(await Guarded(false));
        Console.WriteLine(await Guarded(true));
        Console.WriteLine(s_log);
    }

    static void Main() => Run().GetAwaiter().GetResult();
}
"#,
        "fine\ncaught boom\n2\n",
    );
}

/// A generic local function that is async or an iterator gets a machine
/// generic over the function's own type parameters, not only the owner's.
#[test]
fn a_generic_local_function_has_a_generic_machine() {
    check(
        "RefGenericLocalMachine",
        r#"
using System;
using System.Collections.Generic;
using System.Threading.Tasks;

static class Program
{
    static async Task Main()
    {
        await Show(1);
        await Show("two");
        foreach (var item in Twice('c')) Console.WriteLine(item);

        async Task Show<T>(T value)
        {
            await Task.Yield();
            Console.WriteLine(value);
        }

        IEnumerable<T> Twice<T>(T value)
        {
            yield return value;
            yield return value;
        }
    }
}
"#,
        "1\ntwo\nc\nc\n",
    );
}

/// An extension `GetEnumerator` is called as the extension call it is: the
/// collection converts to its `this` parameter (a struct is boxed), defaults
/// fill its optional parameters, and an internal or static member of the
/// same name does not stand in its way.
#[test]
fn foreach_calls_an_extension_get_enumerator_as_a_call() {
    check(
        "RefForEachExtension",
        r#"
using System;

public struct S
{
    public sealed class Enumerator
    {
        public Enumerator(int start) { Current = start; }
        public int Current { get; private set; }
        public bool MoveNext() => Current++ != 3;
    }
}

public class C
{
    internal S.Enumerator GetEnumerator() => throw null;
}

public class D
{
    public static S.Enumerator GetEnumerator() => throw null;
}

public static class Extensions
{
    public static S.Enumerator GetEnumerator(this object self, int start = 0) => new S.Enumerator(start);
}

static class Program
{
    static void Main()
    {
        foreach (var i in new S()) Console.Write(i);
        Console.WriteLine();
        foreach (var i in new C()) Console.Write(i);
        Console.WriteLine();
        foreach (var i in new D()) Console.Write(i);
        Console.WriteLine();
    }
}
"#,
        "123\n123\n123\n",
    );
}

/// `a ?? b` on a type parameter tests the value boxed, and converts each
/// side to what the whole is.
#[test]
fn a_coalesce_on_a_type_parameter_tests_it_boxed() {
    check(
        "RefCoalesceTypeParameter",
        r#"
using System;

static class Program
{
    static void Show<T>(T first, T second) => Console.WriteLine(first ?? second);

    static void Wider<T1, T2>(T1 first, T2 second) where T1 : T2 => Console.WriteLine(first ?? second);

    static object Boxed(int? first, object second) => first ?? second;

    static void Main()
    {
        Show(0, 1000);
        Show<string>(null, "fallback");
        Show<int?>(null, 4);
        Wider<int?, object>(null, 7);
        Wider<int?, int?>(9, 1000);
        Console.WriteLine(Boxed(5, "x"));
        Console.WriteLine(Boxed(null, "x"));
    }
}
"#,
        "0\nfallback\n4\n7\n9\n5\nx\n",
    );
}

/// `base.F()` inside a lambda reads `this`, so the lambda captures it.
#[test]
fn a_lambda_calling_through_base_captures_this() {
    check(
        "RefBaseInLambda",
        r#"
using System;

class B
{
    public virtual string F() => "base";
}

class C : B
{
    public override string F() => "derived";

    string Call()
    {
        Func<string> f = () => base.F();
        return f();
    }

    static void Main() => Console.WriteLine(new C().Call());
}
"#,
        "base\n",
    );
}

/// Where the conversions leave two candidates level, the one that needs no
/// default filled in wins before genericity is asked.
#[test]
fn a_candidate_without_defaults_beats_a_less_generic_one_with_them() {
    check(
        "RefOverloadDefaults",
        r#"
using System;

static class Program
{
    static int Goo(int x, string y = null) => 1;
    static int Goo<T>(T x) => 0;

    static void Main() => Console.WriteLine(Goo(0));
}
"#,
        "0\n",
    );
}

/// `decimal` converts to and from an enum through the integer underneath,
/// with the operator of each primitive's own width, and `++` on it is
/// `op_Increment`.
#[test]
fn a_decimal_converts_through_its_operators() {
    check(
        "RefDecimalOperators",
        r#"
using System;
using System.Globalization;

enum E { Zero, One, Two }

static class Program
{
    static void Main()
    {
        decimal d = 1.00M;
        Console.WriteLine(((decimal)(E)d).ToString(CultureInfo.InvariantCulture));
        Console.WriteLine((E)((decimal)E.One + 1));
        decimal big = 300m;
        try { Console.WriteLine((byte)big); } catch (OverflowException) { Console.WriteLine("overflow"); }
        Console.WriteLine(((decimal)12345.75f).ToString(CultureInfo.InvariantCulture));
        var x = 1.5m;
        var y = x++;
        --x;
        Console.WriteLine((x + y).ToString(CultureInfo.InvariantCulture));
        Console.WriteLine(-2147483648);
        Console.WriteLine((-9223372036854775808).GetType());
        decimal m = -2147483648;
        Console.WriteLine(m.ToString(CultureInfo.InvariantCulture));
    }
}
"#,
        "1\nTwo\noverflow\n12345.75\n3.0\n-2147483648\nSystem.Int64\n-2147483648\n",
    );
}

/// Named arguments are evaluated in the order they were written, whatever
/// order the parameters take them in.
#[test]
fn named_arguments_are_evaluated_as_written() {
    check(
        "RefNamedArgumentOrder",
        r#"
using System;

static class Program
{
    static int Get(int i) { Console.Write("[" + i + "]"); return i; }
    static int Pair(int x, int y) { Console.Write("(" + x + "," + y + ")"); return x * 10 + y; }

    static void Main()
    {
        Pair(y: Get(1), x: Get(2));
        Console.WriteLine();
        Pair(y: Get(3), x: Pair(y: Get(4), x: Get(5)));
        Console.WriteLine();
    }
}
"#,
        "[1][2](2,1)\n[3][4][5](5,4)(54,3)\n",
    );
}

/// `&` and `|` on `bool?` are three-valued, and `null` beside a value type
/// is that type's `T?`.
#[test]
fn lifted_bool_operators_are_three_valued() {
    check(
        "RefLiftedBool",
        r#"
using System;

static class Program
{
    static string Show(bool? b) => b.HasValue ? b.Value.ToString() : "null";

    static void Main()
    {
        bool? t = true, f = false, n = null;
        Console.WriteLine(Show(f & n) + " " + Show(n & f) + " " + Show(t & n) + " " + Show(t & t));
        Console.WriteLine(Show(t | n) + " " + Show(n | t) + " " + Show(f | n) + " " + Show(f | f));
        Console.WriteLine(Show(false & null) + " " + Show(true | null) + " " + Show(true & null));
        int? sum = 1 + null;
        Console.WriteLine(sum.HasValue);
    }
}
"#,
        "False False null True\nTrue True null False\nFalse True null\nFalse\n",
    );
}

/// `typeof` of an unbound generic type loads its definition, a `default(T)`
/// parameter default is the default of what `T` is at the call, and a
/// constant can be the receiver of a call.
#[test]
fn unbound_typeof_and_defaults_of_type_parameters() {
    check(
        "RefTypeofUnbound",
        r#"
using System;

class Outer<T>
{
    public class Inner<U> { }
    public class Plain { }
    public static void Show()
    {
        Console.WriteLine(typeof(Inner<>));
        Console.WriteLine(typeof(Plain));
    }
    public int Count(T value = default(T)) => value == null ? 0 : 1;
}

static class Program
{
    static string Widened(int? x = default(byte)) => x.HasValue + ":" + x.Value;

    static void Main()
    {
        Console.WriteLine(Widened());
        Console.WriteLine(typeof(Outer<>));
        Console.WriteLine(typeof(void));
        Outer<long>.Show();
        Console.WriteLine(new Outer<string>().Count());
        Console.WriteLine(new Outer<int>().Count());
        Console.WriteLine(int.MaxValue.ToString());
    }
}
"#,
        "True:0\nOuter`1[T]\nSystem.Void\nOuter`1+Inner`1[T,U]\nOuter`1+Plain[System.Int64]\n0\n1\n2147483647\n",
    );
}

/// A local function inside a generic local function names that one's type
/// parameters, which its method declares after the member's.
#[test]
fn a_local_function_inside_a_generic_one_is_generic_too() {
    check(
        "RefNestedGenericLocal",
        r#"
using System;

static class Program
{
    static string Outer<A>()
    {
        static string Middle<B>()
        {
            static string Inner() => typeof(B).Name;
            return Inner();
        }
        return Middle<A>() + "/" + Middle<byte>();
    }

    static void Main() => Console.WriteLine(Outer<string>());
}
"#,
        "String/Byte\n",
    );
}

/// Constant expressions are folded where they are written: a NaN is loaded
/// as the one `csc` writes, a shift counts modulo the width, and a hole's
/// alignment is the value of its constant expression.
#[test]
fn constant_expressions_are_folded() {
    check(
        "RefConstantFolding",
        r#"
using System;

static class Program
{
    static void Main()
    {
        Console.WriteLine(BitConverter.DoubleToInt64Bits(0.0 / 0.0).ToString("X"));
        Console.WriteLine(BitConverter.SingleToInt32Bits(-float.NaN).ToString("X"));
        Console.WriteLine(1 << 33);
        Console.WriteLine(1L << 65);
        Console.WriteLine(double.IsPositiveInfinity(1.0 / 0.0));
        Console.WriteLine($"[{123,-(3 + 4)}]");
    }
}
"#,
        "FFF8000000000000\nFFC00000\n2\n2\nTrue\n[123    ]\n",
    );
}

/// A compound assignment on a `T`'s property reads the receiver once: a
/// class-constrained `T` goes through an address for its `constrained.`
/// call, and an unconstrained one keeps the reference it read where it
/// turns out to be a class.
#[test]
fn a_type_parameter_receiver_is_read_once() {
    check(
        "RefTypeParameterReceiver",
        r#"
using System;

interface I { int P { get; set; } }

class C : I
{
    public int F;
    public int P
    {
        get { Console.Write(F); Program.Field = new C { F = Program.Field.F + 1 }; return 0; }
        set { Console.Write(F); }
    }
}

struct S : I
{
    public int F;
    public int P { get => F; set => F = value; }
}

static class Program
{
    public static C Field;

    static void Any<T>(ref T f) where T : I { f.P += 1; }
    static void Class<T>(ref T f) where T : class, I { f.P += 1; }

    static void Main()
    {
        Field = new C { F = 1 };
        Any(ref Field);
        Console.WriteLine(":" + Field.F);
        Field = new C { F = 1 };
        Class(ref Field);
        Console.WriteLine(":" + Field.F);
        var s = new S { F = 5 };
        Any(ref s);
        Console.WriteLine(s.F);
    }
}
"#,
        "11:2\n11:2\n6\n",
    );
}

/// `base.F` as a delegate is the base's method, and a lambda in a
/// constructor initializer has its display class made before the call.
#[test]
fn base_method_groups_and_lambdas_before_this() {
    check(
        "RefBaseDelegate",
        r#"
using System;

class B { public virtual string F() => "base"; }

class C : B
{
    int x;
    public override string F() => "derived";

    C(int x) : this(z => x + z) { this.x = x; }
    C(Func<int, int> f) { Console.WriteLine(f(10)); }

    static void Main()
    {
        var c = new C(1);
        Func<string> f = ((B)c).F;
        Console.WriteLine(f());
        c.Show();
        decimal? missing = null;
        Console.WriteLine(missing ?? default(decimal));
    }

    void Show()
    {
        Func<string> f = base.F;
        Console.WriteLine(f());
    }
}
"#,
        "11\nderived\nbase\n0\n",
    );
}

/// Operands are promoted before a unary operator, an enum sum over a `byte`
/// is narrowed back (and overflows where checked), an `S?` whose `S`
/// reaches the right side's type coalesces to that type, and `nuint`
/// constants and conversions zero-extend what is unsigned.
#[test]
fn promotions_and_narrowings_of_operators() {
    check(
        "RefPromotions",
        r#"
using System;

enum Color : byte { Red, Green, Blue }

struct Point
{
    public static implicit operator int(Point p) { Console.Write("op "); return 7; }
}

static class Program
{
    static void Main()
    {
        byte small = 3;
        Console.WriteLine((-small).GetType().Name + " " + (-(2147483648)).GetType().Name + " " + (~small).GetType().Name);
        Color c = Color.Blue;
        byte b = 254;
        Console.WriteLine(unchecked(c + b));
        try { Console.WriteLine(checked(c + b)); } catch (OverflowException) { Console.WriteLine("overflow"); }
        Console.WriteLine((0 - c).GetType().Name + " " + (c - 1).GetType().Name);
        Point? p = new Point();
        Point? none = null;
        Console.WriteLine(p ?? -1);
        Console.WriteLine(none ?? -1);
        nuint[] wide = { uint.MaxValue, 1 };
        uint u = uint.MaxValue;
        nuint fromU = u;
        long fromN = (long)fromU;
        Console.WriteLine(wide[0] + " " + fromU + " " + fromN);
        int i, j;
        for (i = 0, j = 10; i < 3; i++) j++;
        Console.WriteLine(i + " " + j);
        {
            int f() => 1;
            Console.Write(f());
        }
        {
            int f() => 2;
            Func<int> g = f;
            Console.WriteLine(f() + "" + g());
        }
    }
}
"#,
        "Int32 Int64 Int32\nRed\noverflow\nByte Color\nop 7\n-1\n4294967295 4294967295 4294967295\n3 13\n122\n",
    );
}

/// User-defined conversions where the language picks them: a cast prefers
/// the explicit operator taking exactly the operand, `++` from a base's
/// operator converts back to the variable's type, `"S" + t` concatenates
/// what `t` converts to, and `b ^ true` is `!b`.
#[test]
fn user_defined_conversions_where_the_language_picks_them() {
    check(
        "RefUserConversions",
        r#"
using System;
using System.Collections.Generic;

struct Str
{
    public int Num;
    public static explicit operator Str(int i) => new Str { Num = 10 };
    public static implicit operator Str(double d) => new Str { Num = 100 };
}

class A
{
    public static C operator ++(A x) { Console.Write("inc "); return new C(); }
}

class C : A
{
    public static implicit operator B(C x) { Console.Write("conv "); return new B(); }
}

class B : A { }

class T
{
    public static implicit operator string(T t) => "T";
}

static class Program
{
    static void Main()
    {
        Console.WriteLine(((Str)1).Num);
        B b = new B();
        b++;
        Console.WriteLine(b.GetType().Name);
        Console.WriteLine("S" + new T());
        bool yes = true;
        Console.WriteLine(yes ^ true);
        int[] ints = { 1 };
        IList<int> list = new List<int> { 2 };
        var both = new[] { ints, list };
        Console.WriteLine(both.GetType().Name);
    }
}
"#,
        "10\ninc conv B\nST\nFalse\nIList`1[]\n",
    );
}

/// A `bool` holding 0xFF is still `true` however it is compared or read
/// through a reference; a static property of a generic type is called, not
/// dispatched; a field-like event's initializer runs; and `new T { ... }`
/// initializes the object itself.
#[test]
fn values_reach_where_they_are_written() {
    check(
        "RefValuesReach",
        r#"
using System;

class G<T>
{
    public static string S { get; set; }
}

struct Holder
{
    static event Action E = Nothing;
    static void Nothing() { }
    public static bool Wired => E != null;
}

class C
{
    public int Field;
    public static int Make<T>() where T : C, new() => new T { Field = 42 }.Field;
}

static class Program
{
    static bool Read(ref bool b) => b;

    static void Main()
    {
        byte[] bytes = { 0xFF };
        bool[] flags = { true };
        Buffer.BlockCopy(bytes, 0, flags, 0, 1);
        Console.WriteLine((flags[0] == true) + " " + (flags[0] != true) + " " + (flags[0] ^ Read(ref flags[0])));
        G<int>.S = "int";
        G<string>.S = "string";
        Console.WriteLine(G<int>.S + " " + G<string>.S);
        Console.WriteLine(Holder.Wired);
        Console.WriteLine(C.Make<C>());
    }
}
"#,
        "True False False\nint string\nTrue\n42\n",
    );
}

/// An anonymous type is laid out and hashed as `csc` lays it out: its
/// values in `readonly` `<x>i__Field` fields, a hash seeded from those names,
/// and `new { }` a type of its own.
#[test]
fn anonymous_types_are_laid_out_as_csc_does() {
    check(
        "RefAnonymousLayout",
        r#"
using System;
using System.Reflection;

static class Program
{
    static void Main()
    {
        var pair = new { a = 1, b = "x" };
        foreach (var field in pair.GetType().GetFields(BindingFlags.Instance | BindingFlags.NonPublic))
            Console.WriteLine(field.Attributes + " " + field.Name);
        var empty = new { };
        Console.WriteLine(empty + " " + empty.GetHashCode());
        Console.WriteLine(new { a = 1 }.GetHashCode() == new { b = 1 }.GetHashCode());
        Console.WriteLine(new { a = 1 }.GetHashCode() == new { a = 1 }.GetHashCode());
    }
}
"#,
        "Private, InitOnly <a>i__Field\nPrivate, InitOnly <b>i__Field\n{ } 0\nFalse\nTrue\n",
    );
}

/// An override's type parameters carry the constraints of the method it
/// overrides, written in the derived type's terms: `where S : T` of an
/// `A<T>` is `where S : int?` under `C : A<int?>`.
#[test]
fn an_override_inherits_constraints_in_its_own_terms() {
    check(
        "RefInheritedConstraints",
        r#"
using System;

class A<T>
{
    public virtual string M<S>(S x) where S : T => "A";
}

class C : A<int?>
{
    public override string M<S>(S x) => x is ValueType ? "value" : "null";

    static void Main()
    {
        A<int?> c = new C();
        Console.WriteLine(c.M<int?>(null) + " " + c.M<int?>(1));
    }
}
"#,
        "null value\n",
    );
}

/// A type implements every interface its interfaces inherit, so listing
/// `I2 : I1` re-implements `I1` and a public method takes over from the
/// base's explicit implementation.
#[test]
fn an_inherited_interface_is_implemented_afresh() {
    check(
        "RefReimplementation",
        r#"
using System;

interface I1 { string Goo(); }
interface I2 : I1 { }

class X : I1 { string I1.Goo() => "X"; }
class Y : X, I2 { public virtual string Goo() => "Y"; }

static class Program
{
    static void Main()
    {
        I1 i = new Y();
        Console.WriteLine(i.Goo());
    }
}
"#,
        "Y\n",
    );
}

/// An `await` inside `?.` and `??` runs only where the operand it is in is
/// evaluated, and `?.` on a `T` that is a struct works on the element
/// itself, not on a copy.
#[test]
fn awaits_in_conditional_operands_and_struct_receivers() {
    check(
        "RefConditionalAwait",
        r#"
using System;
using System.Threading.Tasks;

interface IToggle { IToggle Toggle(int i); }

struct Flag : IToggle
{
    bool on;
    public IToggle Toggle(int i) { Console.Write(on + " "); on = !on; return this; }
}

static class Program
{
    static int calls;
    static async Task<int> Val() { await Task.Yield(); calls++; return 1; }

    static async Task<int> Length(string s) => s?.Length + await Val() ?? await Val() + 10;

    static async Task Twice<T>(T[] items) where T : IToggle
    {
        items[0]?.Toggle(await Val());
        items[0]?.Toggle(await Val());
    }

    static void Sync<T>(T[] items) where T : IToggle
    {
        items[0]?.Toggle(0);
        items[0]?.Toggle(0);
    }

    static async Task Main()
    {
        Console.WriteLine(await Length(null) + " " + calls);
        Console.WriteLine(await Length("ab") + " " + calls);
        await Twice(new Flag[1]);
        Console.WriteLine();
        Sync(new Flag[1]);
        Console.WriteLine();
    }
}
"#,
        "11 2\n3 3\nFalse True \nFalse True \n",
    );
}

/// Only a `Main` of the right shape is an entry point, and a synchronous one
/// is preferred to an `async` one beside it.
#[test]
fn the_entry_point_is_the_main_of_the_right_shape() {
    check(
        "RefEntryPoint",
        r#"
using System;
using System.Threading.Tasks;

class Program
{
    static void Main() => Console.WriteLine("sync");
    static async Task Main(string[] args) { await Task.Yield(); Console.WriteLine("async"); }
}

class Other
{
    static void Main<T>() => Console.WriteLine("generic");
    static void Main(int wrong) => Console.WriteLine("wrong");
}
"#,
        "sync\n",
    );
}

/// A method group in an expression tree is the method asked for a
/// delegate: `MethodInfo.CreateDelegate`, which the compiled tree then runs.
#[test]
fn a_method_group_in_an_expression_tree_creates_the_delegate() {
    check(
        "RefTreeMethodGroup",
        r#"
using System;
using System.Linq.Expressions;

class C
{
    int offset = 100;
    int Add(int x) => x + offset;
    static int Twice(int x) => x * 2;

    static void Main()
    {
        Expression<Func<int, Func<int, int>>> e = x => Twice;
        Console.WriteLine(e.Compile()(0)(21));
        var c = new C();
        Expression<Func<Func<int, int>>> bound = () => c.Add;
        Console.WriteLine(bound.Compile()()(5));
        Console.WriteLine(e.Body.NodeType);
        Expression<Func<int, string, string>> text = (n, s) => $"{{n={n:D2}}} {s}";
        Console.WriteLine(text.Compile()(5, "x") + " " + text.Body.NodeType);
    }
}
"#,
        "42\n105\nConvert\n{n=05} x Call\n",
    );
}

/// A `decimal` literal with more digits than a `decimal` holds is rounded to
/// the nearest one it can, however many digits it wrote.
#[test]
fn a_long_decimal_literal_is_rounded_once() {
    check(
        "RefDecimalLiteral",
        r#"
using System;
using System.Globalization;

static class Program
{
    static void Show(decimal d) => Console.WriteLine(d.ToString(CultureInfo.InvariantCulture));

    static void Main()
    {
        Show(.10000000000000000000000000005000000000000000000001m);
        Show(3.0500000000000000000001e-27m);
        Show(1e-30m);
        Show(0.50m);
    }
}
"#,
        "0.1000000000000000000000000001\n0.0000000000000000000000000031\n0.0000000000000000000000000000\n0.50\n",
    );
}

/// `delegate { ... }` with no parameter list is given to a delegate of any
/// parameters, and a generic method group names its type arguments.
#[test]
fn anonymous_methods_and_generic_method_groups() {
    check(
        "RefAnonymousMethod",
        r#"
using System;

static class Program
{
    static string Name<T>() => typeof(T).Name;

    static void Main()
    {
        Func<string, int, int> f = delegate { return 9; };
        Console.WriteLine(f("x", 1));
        Func<string> g = Name<int>;
        Console.WriteLine(g());
        static string Local<T>() => typeof(T).Name;
        Func<string> h = Local<string>;
        Console.WriteLine(h());
    }
}
"#,
        "9\nInt32\nString\n",
    );
}

/// A cast of a lambda or a method group reaches an operator taking a
/// delegate: the operand becomes that delegate first.
#[test]
fn a_cast_makes_a_delegate_for_an_operator() {
    check(
        "RefCastThroughDelegate",
        r#"
using System;

class C
{
    public string Text;
    public static explicit operator C(Func<string, string> f) => new C { Text = f("A") };
    static string Lower(string s) => s.ToLower();

    static void Main()
    {
        Console.WriteLine(((C)Lower).Text);
        Console.WriteLine(((C)(s => s + s)).Text);
    }
}
"#,
        "a\nAA\n",
    );
}

/// A derived `GetEnumerator(params int[])` overloads the base's
/// `GetEnumerator()` rather than hiding it, and `foreach` takes the base's.
#[test]
fn foreach_finds_a_parameterless_get_enumerator_past_an_overload() {
    check(
        "RefForEachOverload",
        r#"
using System;
using System.Collections.Generic;

class A
{
    public List<string>.Enumerator GetEnumerator() => new List<string> { "a", "b" }.GetEnumerator();
}

class B : A
{
    public List<int>.Enumerator GetEnumerator(params int[] x) => new List<int>().GetEnumerator();
}

static class Program
{
    static void Main()
    {
        foreach (var x in new B()) Console.Write(x.ToUpper());
        Console.WriteLine();
    }
}
"#,
        "AB\n",
    );
}

/// A capturing lambda inside a generic local function is a generic method
/// of the display class, over the function's type parameters; and the local
/// function itself is named through its generic signature.
#[test]
fn a_lambda_inside_a_generic_local_function_is_generic() {
    check(
        "RefLambdaInGenericLocal",
        r#"
using System;

static class Program
{
    static void Run<TFirst, TSecond>(TFirst first, TSecond second, Func<TFirst, TSecond, string> f)
        => Console.WriteLine(f(first, second) + "-" + typeof(TFirst).Name);

    static void Test<T>(T param)
    {
        var message = "m";
        void Local<TLocal>(TLocal value)
        {
            Run(value, param, (_, __) => message);
            Run(new TLocal[] { value }, param, (_, __) => message);
        }
        Local("s");
        Local(1);
    }

    static void Main() => Test(2.5);
}
"#,
        "m-String\nm-String[]\nm-Int32\nm-Int32[]\n",
    );
}

/// Compound assignment and `++` on a nullable variable are lifted: a null
/// on either side gives a null, and otherwise the value inside is changed.
#[test]
fn compound_assignment_on_a_nullable_is_lifted() {
    check(
        "RefLiftedCompound",
        r#"
using System;

struct S
{
    public int V;
    public static S operator ++(S s) => new S { V = s.V + 10 };
}

static class Program
{
    static void Main()
    {
        int? n = 1;
        int a = 2;
        n += a;
        Console.WriteLine(n);
        int? e = null;
        n += e;
        Console.WriteLine(n.HasValue);
        int? m = 5;
        Console.WriteLine(m++);
        Console.WriteLine(++m);
        m = null;
        m--;
        Console.WriteLine(m.HasValue);
        byte? b = 250;
        b += 10;
        Console.WriteLine(b);
        S? s = new S { V = 1 };
        s++;
        Console.WriteLine(s.Value.V);
    }
}
"#,
        "3\nFalse\n5\n7\nFalse\n4\n11\n",
    );
}

/// A unary operator a struct declares lifts onto its `S?`, and `e - 0` on an
/// enum is `E - E` unless the zero already is the underlying type.
#[test]
fn lifted_user_unary_and_enum_minus_zero() {
    check(
        "RefLiftedUnaryEnumZero",
        r#"
using System;

enum E : short { }

struct S
{
    public static int operator +(S s) => 1;
    public static bool operator !(S s) => true;
}

static class Program
{
    static void Print<T>(T value) => Console.WriteLine(typeof(T).Name);

    static void Main()
    {
        S? some = new S();
        S? none = null;
        Console.WriteLine(+some);
        Console.WriteLine((+none).HasValue);
        Console.WriteLine(!some);
        E x = 0;
        E? y = 0;
        const short zero = 0;
        Print(x - 0);
        Print(x - zero);
        Print(x - 1);
        Print(y - zero);
    }
}
"#,
        "1\nFalse\nTrue\nInt16\nE\nE\nNullable`1\n",
    );
}

/// An override past a method metadata cannot tell apart from it (`M(out
/// int)` hiding `M(ref int)`) names what it overrides; and a private
/// extension method in another class is no candidate.
#[test]
fn overrides_past_a_hiding_method_and_inaccessible_extensions() {
    check(
        "RefOverrideRefOut",
        r#"
using System;
using System.Linq;

class Ref1 { public virtual void M(ref int x) { x = 1; } }
class Out1 : Ref1 { public new virtual void M(out int x) { x = 2; } }
class Ref2 : Out1 { public override void M(ref int x) { x = 3; } }
class Out2 : Ref2 { public override void M(out int x) { x = 4; } }

static class Extensions
{
    private static bool Contains<T>(this System.Collections.Generic.IEnumerable<T> a, T value)
        => throw new NotImplementedException();
}

static class Program
{
    static void Main()
    {
        int x = 0;
        Ref1 r1 = new Out2();
        r1.M(ref x);
        Console.Write(x);
        Out1 o1 = new Ref2();
        o1.M(out x);
        Console.Write(x);
        o1 = new Out2();
        o1.M(out x);
        Console.Write(x);
        o1.M(ref x);
        Console.WriteLine(x);
        var a = new[] { 0, 1, 3 };
        Console.WriteLine(new[] { 1, 2, 3 }.Count(a.Contains));
    }
}
"#,
        "3243\n2\n",
    );
}

/// User-defined conversions around a nullable, `++` through a conversion to
/// a number and back, and a downcast preferred over a user-defined operator.
#[test]
fn casts_and_increments_through_user_defined_conversions() {
    check(
        "RefUserConversionShapes",
        r#"
using System;

class A
{
    public A(string text) { Text = text; }
    public readonly string Text;
    public static implicit operator short(A x) => short.Parse(x.Text);
    public static implicit operator A(short x) => new A(x.ToString());
    public override string ToString() => "A" + Text;
}

class C
{
    public readonly int V;
    public C(int v) { V = v; }
    public static implicit operator C(int v) => new C(v);
}

struct S
{
    public string Text;
    public static implicit operator S?(string x) => new S { Text = x.ToLower() };
}

class Base<T> { }
class Derived<T> : Base<T>
{
    public static implicit operator Derived<T>(Base<int> x) => null;
}

static class Program
{
    static void Main()
    {
        var a = new A("5");
        Console.Write((object)(a++));
        Console.Write((object)a);
        Console.Write((object)(--a));
        Console.WriteLine((object)a);
        int? i = 7;
        Console.WriteLine(((C)i).V);
        Console.WriteLine(((S)"XY").Text);
        Base<int> b = new Derived<int>();
        Console.WriteLine((Derived<int>)b == null);
    }
}
"#,
        "A5A6A5A5\n7\nxy\nFalse\n",
    );
}

/// Member lookup on a type parameter: the effective base class's members
/// come before the interfaces', whatever order the constraints are written
/// in, and an interface's member hides the `object` one of its signature.
#[test]
fn lookup_on_a_type_parameter_prefers_class_then_interface() {
    check(
        "RefTypeParameterLookup",
        r#"
using System;

interface I { void M(); }
interface IGoo { string ToString(); }
class A { internal void M() { Console.WriteLine("A.M"); } }
class B : A, I, IGoo
{
    void I.M() { Console.WriteLine("B.M"); }
    public override string ToString() => "B";
    string IGoo.ToString() => "IGoo";
}

static class Program
{
    static void Run<T1, T2, T3>(T1 t1, T3 t3) where T1 : I where T2 : A where T3 : T1, T2
    {
        t1.M();
        t3.M();
    }

    static void Show<U>(U u) where U : A, IGoo
    {
        Console.WriteLine(u.ToString());
        Console.WriteLine(u.Equals(u));
    }

    static void Main()
    {
        var b = new B();
        Run<B, B, B>(b, b);
        Show(b);
    }
}
"#,
        "B.M\nA.M\nIGoo\nTrue\n",
    );
}

/// A candidate the argument names cannot be placed into is no candidate:
/// a name it lacks, a parameter given twice, or a non-trailing named
/// argument out of its position.
#[test]
fn argument_names_rule_out_candidates() {
    check(
        "RefNamesRuleOut",
        r#"
using System;

class C
{
    public C(object c, object o) => Console.Write("object ");
    public C(int i, object o) => Console.Write("int ");

    static void M(int a, int b) => Console.Write($"First {a} {b}. ");
    static void M(long b, long a) => Console.Write($"Second {b} {a}. ");

    static void N(int a = 1, int b = 2, int c = 3) => Console.Write("three ");
    static void N(long c = 1, long b = 2) => Console.Write($"two {c} {b}. ");

    static void Main()
    {
        M(a: 1, 2);
        M(3, a: 4);
        N(c: 5, 6);
        C made = new(c: new(), 2);
        Console.WriteLine();
    }
}
"#,
        "First 1 2. Second 3 4. two 5 6. object \n",
    );
}

/// `&&` and `||` on a type that declares `&`, `|`, `true` and `false`
/// (inherited ones included) test the left operand once and combine only
/// where it does not decide.
#[test]
fn user_defined_conditional_logical_operators() {
    check(
        "RefUserShortCircuit",
        r#"
using System;

public class Base
{
    public static bool operator true(Base x) { Console.Write("T"); return x.Value; }
    public static bool operator false(Base x) { Console.Write("F"); return !x.Value; }
    public bool Value;
}

public class Derived : Base
{
    public string Name = "";
    public static Derived operator &(Derived x, Derived y) { Console.Write("&"); return y; }
    public static Derived operator |(Derived x, Derived y) { Console.Write("|"); return y; }

    static Derived Make(string name, bool value) { Console.Write(name); return new Derived { Name = name, Value = value }; }

    static void Main()
    {
        var r = Make("a", true) && Make("b", false);
        Console.WriteLine(" " + r.Name);
        r = Make("c", false) && Make("d", true);
        Console.WriteLine(" " + r.Name);
        r = Make("e", true) || Make("f", false);
        Console.WriteLine(" " + r.Name);
        r = Make("g", false) || Make("h", true);
        Console.WriteLine(" " + r.Name);
    }
}
"#,
        "aFb& b\ncF c\neT e\ngTh| h\n",
    );
}

/// An indexer initializer whose key holds braces of its own — an object
/// initializer, a lambda body — is still `[key] = value`.
#[test]
fn an_indexer_initializer_key_may_hold_braces() {
    check(
        "RefBracedIndexerKey",
        r#"
using System;
using System.Collections.Generic;

class C
{
    public int I;

    static void Main()
    {
        var d = new Dictionary<C, int> { [new C { I = 3 }] = 7 };
        foreach (var pair in d) Console.WriteLine(pair.Key.I + " " + pair.Value);
        var f = new Dictionary<Func<int>, string> { [() => { return 4; }] = "four" };
        foreach (var pair in f) Console.WriteLine(pair.Key() + " " + pair.Value);
    }
}
"#,
        "3 7\n4 four\n",
    );
}

/// A delegate has `BeginInvoke` and `EndInvoke` beside `Invoke`, the second
/// taking the `ref` and `out` parameters back.
#[test]
fn a_delegate_has_begin_and_end_invoke() {
    check(
        "RefDelegateAsyncMembers",
        r#"
using System;
using System.Linq;
using System.Reflection;

delegate T D<T>(ref int x, out string s, long y);

static class Program
{
    static void Main()
    {
        foreach (var member in typeof(D<>).GetMembers(
            BindingFlags.DeclaredOnly | BindingFlags.Public | BindingFlags.Instance).OrderBy(m => m.MetadataToken))
        {
            Console.WriteLine(member.ToString());
        }
        D<int> d = (ref int x, out string s, long y) => { s = "s"; return x + (int)y; };
        int a = 1;
        Console.WriteLine(d(ref a, out var text, 2) + text);
    }
}
"#,
        "Void .ctor(System.Object, IntPtr)\nT Invoke(Int32 ByRef, System.String ByRef, Int64)\nSystem.IAsyncResult BeginInvoke(Int32 ByRef, System.String ByRef, Int64, System.AsyncCallback, System.Object)\nT EndInvoke(Int32 ByRef, System.String ByRef, System.IAsyncResult)\n3s\n",
    );
}

/// Extension methods: the enclosing namespace's own classes are searched
/// before its imports, and the receiver does not widen as a number; and a
/// `goto` to a label right in front of a `try` leaves it through `finally`.
#[test]
fn extension_scopes_receivers_and_goto_before_try() {
    check(
        "RefExtensionScopes",
        r#"
using System;
using N;

static class Program
{
    static void Main()
    {
        "".Goo(1);
        0.Bar();
        int i = 0;
        try
        {
        L:
            try
            {
                i++;
                goto L;
            }
            finally
            {
                if (i == 3) throw new Exception();
            }
        }
        catch (Exception)
        {
            Console.WriteLine("caught " + i);
        }
    }

    public static void Goo(this string x, object y) => Console.WriteLine("own");
    static void Bar(this long x) => Console.WriteLine("long");
    static void Bar(this object x) => Console.WriteLine("object");
}

namespace N
{
    static class C
    {
        public static void Goo(this string x, int y) => Console.WriteLine("imported");
    }
}
"#,
        "own\nobject\ncaught 3\n",
    );
}

/// A struct's operator taking its own `S?` is found for an `S?` operand
/// before the lifted form of the one taking `S`; and a constant pattern on
/// an `nint` compares native integers.
#[test]
fn nullable_operand_operators_and_native_integer_cases() {
    check(
        "RefNullableOperandNint",
        r#"
using System;

struct S
{
    public static int operator -(S s) => 2;
    public static int operator -(S? s) => s.HasValue ? 20 : -20;
    public static int operator ~(S s) => 4;
}

static class Program
{
    static void Main()
    {
        S? some = new S();
        S? none = null;
        Console.WriteLine(-some + " " + -none);
        Console.WriteLine((~some) + " " + (~none).HasValue);
        nint n = 6;
        switch (n)
        {
            case 0: Console.WriteLine("zero"); break;
            case 6: Console.WriteLine("six"); break;
            default: Console.WriteLine("other"); break;
        }
        Console.WriteLine(n is 6);
    }
}
"#,
        "20 -20\n4 False\nsix\nTrue\n",
    );
}

/// A partial property is one property: the implementing part's accessors,
/// with the defining part's view of the parameters; and an indexer takes a
/// `params` array one index at a time.
#[test]
fn partial_properties_and_params_indexers() {
    check(
        "RefPartialProperties",
        r#"
using System;

partial class C
{
    private partial int P { get; }
    public partial int this[int x, string label = "default"] { get; }
    public int this[params int[] values] { get { return values.Length; } }

    static void Main()
    {
        var c = new C();
        Console.WriteLine(c.P);
        Console.WriteLine(c[1]);
        Console.WriteLine(c[1, 2, 3]);
        Console.WriteLine(c[new[] { 4, 5 }]);
    }
}

partial class C
{
    private partial int P { get => 7; }
    public partial int this[int y, string text]
    {
        get { Console.Write(text + " "); return y; }
    }
}
"#,
        "7\ndefault 1\n3\n2\n",
    );
}

/// The predefined operators are reached through an operand's user-defined
/// conversions, lifted over nullables, in binary operators and compound
/// assignments alike.
#[test]
fn predefined_operators_through_user_defined_conversions() {
    check(
        "RefOperatorsThroughConversions",
        r#"
using System;

struct IntHolder
{
    private int x;
    public static implicit operator int(IntHolder h) { Console.Write("to "); return h.x; }
    public static implicit operator IntHolder(int i) { Console.Write("from "); return new IntHolder { x = i }; }
    public override string ToString() => x.ToString();
}

public struct EnumWrapper<T> where T : struct
{
    public T? Enum { get; private set; }
    public static implicit operator T?(EnumWrapper<T> w) => w.Enum;
    public static implicit operator EnumWrapper<T>(T source) => new EnumWrapper<T> { Enum = source };
}

[Flags]
public enum Flags { None = 0, A = 1, B = 2 }

static class Program
{
    static void Main()
    {
        IntHolder h = 5;
        Console.WriteLine(h + 1);
        IntHolder? y = 0;
        y += 5;
        Console.WriteLine(y);
        IntHolder? none = null;
        none += 1;
        Console.WriteLine(none.HasValue);
        EnumWrapper<Flags> wrapped = Flags.A;
        wrapped |= Flags.B;
        Console.WriteLine(wrapped.Enum);
    }
}
"#,
        "from to 6\nfrom to from 5\nFalse\nA, B\n",
    );
}

/// `await task;` is an await, not a local of a type called `await`; and
/// the implementing part of a generic partial method names its own type
/// parameters.
#[test]
fn await_statements_and_partial_method_type_parameters() {
    check(
        "RefAwaitStatement",
        r#"
using System;
using System.Threading.Tasks;

static partial class Program
{
    static partial void Show<T>(T value);
    static partial void Show<TValue>(TValue value)
    {
        TValue copy = value;
        Console.WriteLine(copy + " " + typeof(TValue).Name);
    }

    static async Task Main()
    {
        Task task = Task.CompletedTask;
        await task;
        if (task != null) await task;
        Show(3);
        Console.WriteLine("done");
    }
}
"#,
        "3 Int32\ndone\n",
    );
}

/// Assorted conversions and operators: shifts and constants on native
/// integers, `object + null`, a condition reaching `bool` through a base
/// class's conversion, and an operator taking `int?` given an `int`.
#[test]
fn native_shifts_null_concatenation_and_conditions_by_conversion() {
    check(
        "RefConditionConversions",
        r#"
using System;
using System.Collections.Generic;
using System.Linq;

class B { public static implicit operator bool(B b) => true; }
class A : B { }

struct S
{
    public static int Seen;
    public static implicit operator S(int? value) { Seen = value ?? -1; return new S(); }
}

static class Program
{
    static nuint Add(nuint x, nuint y) => x + y;
    static IEnumerable<(T, U)> Pairs<T, U>(this (IEnumerable<T> xs, IEnumerable<U> ys) source)
        => source.xs.Zip(source.ys, (x, y) => (x, y));

    static void Main()
    {
        nint n = 3;
        Console.WriteLine((n << 2) + " " + (n >> 1) + " " + Add(3, 4));
        object o = "o";
        Console.WriteLine(o + null + "|");
        if (new A()) Console.WriteLine("condition");
        S? s = 123;
        Console.WriteLine(S.Seen + " " + s.HasValue);
        var pair = (new[] { 1, 2 }, new[] { "a", "b" });
        Console.WriteLine(string.Join(",", pair.Pairs()));
    }
}
"#,
        "12 1 7\no|\ncondition\n123 True\n(1, a),(2, b)\n",
    );
}

/// An override that declares one accessor still has the other: reading or
/// writing through it calls the accessor it overrides.
#[test]
fn an_override_with_one_accessor_keeps_the_other() {
    check(
        "RefOverrideOneAccessor",
        r#"
using System;

public class Base1
{
    public virtual long P
    {
        get { Console.Write("Base.get "); return 1; }
        set { Console.Write("Base.set(" + value + ") "); }
    }
}

public abstract class Base2 : Base1
{
    public abstract override long P { get; }
}

public class Derived : Base2
{
    public override long P
    {
        get { Console.Write("Derived.get "); return 5; }
    }
}

static class Program
{
    static void Main()
    {
        Base2 b = new Derived();
        b.P += 1;
        Console.WriteLine();
        Derived d = new Derived();
        d.P = 3;
        Console.WriteLine();
    }
}
"#,
        "Derived.get Base.set(6) \nBase.set(3) \n",
    );
}

/// `using` over a null, `foreach (var x in grid)` over a `double[,]`, a
/// type test on a `void` call, and names qualified through an alias.
#[test]
fn null_usings_grid_walks_and_alias_qualified_names() {
    check(
        "RefAliasQualified",
        r#"
using System;
using NT = Space;

namespace Space
{
    public class Program
    {
        static int counter;
        static void Increment() => counter++;
        public static int Two() => 2;

        public static void Main()
        {
            using (null) { Console.Write("in "); }
            using (IDisposable d = null) { Console.WriteLine("in"); }
            double[,] grid = { { 1.5, 2.5 }, { 3.5, 4.5 } };
            foreach (var x in grid) Console.Write(x.ToString(System.Globalization.CultureInfo.InvariantCulture) + " ");
            Console.WriteLine();
            Func<bool> test = () => Increment() is object;
            Console.WriteLine(test() + " " + counter);
            global::System.Console.WriteLine(NT::Program.Two());
        }
    }
}
"#,
        "in in\n1.5 2.5 3.5 4.5 \nFalse 1\n2\n",
    );
}

/// An enum nested in a generic class is constructed with the class's
/// arguments; and by-reference arguments named out of order have their
/// arrays and indices evaluated as written.
#[test]
fn nested_enums_of_generic_types_and_ref_arguments_out_of_order() {
    check(
        "RefNestedGenericEnum",
        r#"
using System;
using Alias = Outer<string>;

public class Outer<T>
{
    [Flags] public enum E : byte { None = 0, A = 1, B = 2 }
    public E Field = E.A;
    public E Combine(E x) => Field | x;
}

static class Program
{
    static int[] array = new int[1];
    static int[] GetArray(string name) { Console.Write(name + " "); return array; }
    static int GetIndex(string name) { Console.Write(name + " "); return 0; }
    static void Goo(ref int x, out int y) { x = 1; y = 2; }

    static void Main()
    {
        Console.WriteLine(typeof(Outer<int>.E) + " " + typeof(Alias.E) + " " + typeof(Outer<>.E));
        var o = new Outer<int>();
        Console.WriteLine(o.Combine(Outer<int>.E.B) + " " + default(Outer<string>.E));
        Goo(y: out GetArray("A")[GetIndex("B")], x: ref GetArray("C")[GetIndex("D")]);
        Console.WriteLine(array[0]);
    }
}
"#,
        "Outer`1+E[System.Int32] Outer`1+E[System.String] Outer`1+E[T]\nA, B None\nA B C D 2\n",
    );
}

/// Inside a `readonly` member of a struct, a member that may change `this`
/// is called on a copy, and an event is added to through its accessor on a
/// copy too.
#[test]
fn readonly_members_call_mutating_members_on_a_copy() {
    check(
        "RefReadonlyMemberCopy",
        r#"
using System;

public struct S
{
    public int i;
    public event Action E;

    public readonly int P
    {
        get
        {
            M();
            _ = Q;
            Console.Write(i + " ");
            var copy = this;
            copy.M();
            Console.Write(copy.i + " ");
            return i;
        }
    }

    int Q => i = 7;
    void M() { i = 23; }

    public readonly void AddHandler()
    {
        E += () => { };
        Console.Write((E is null) + " ");
        var copy = this;
        copy.E += () => { };
        Console.WriteLine(copy.E is null);
    }

    static void Main()
    {
        var s = new S { i = 1 };
        Console.WriteLine(s.P);
        s.AddHandler();
    }
}
"#,
        "1 23 1\nTrue False\n",
    );
}

/// `f[^1] += 1` on a `ref T` struct indexes the variable itself, not a
/// copy: what `Length` and the indexer do to the struct stays in it.
#[test]
fn a_counted_index_on_a_ref_struct_indexes_the_variable() {
    check(
        "RefCountedIndexRef",
        r#"
using System;

interface I1
{
    int this[int x] { get; set; }
    int Length { get; }
}

struct S1 : I1
{
    public int F1;
    public int this[int x]
    {
        get { Console.Write(F1 + " "); F1++; return 0; }
        set { Console.Write(F1 + " "); }
    }
    public int Length { get { F1++; return 5; } }
}

static class Program
{
    static void Test<T>(ref T f) where T : I1 => f[^1] += 1;

    static void Main()
    {
        var s = new S1 { F1 = 1 };
        Test(ref s);
        Console.WriteLine(s.F1);
    }
}
"#,
        "2 3 3\n",
    );
}

/// A field-like event is invoked as the delegate it holds, and a collection
/// initializer's `Add` may be an extension method, reached by boxing.
#[test]
fn field_like_event_invocation_and_extension_add() {
    check(
        "RefEventInvokeExtensionAdd",
        r#"
using System;
using System.Collections;

interface IAppend { void Append(object o); }

struct Bag : IEnumerable, IAppend
{
    IEnumerator IEnumerable.GetEnumerator() => null;
    void IAppend.Append(object o) { }
}

class C
{
    event Func<string> E;

    void Fire() => Console.WriteLine(E != null ? E() : "none");

    static void Main()
    {
        var c = new C();
        c.Fire();
        c.E += () => "handled";
        c.Fire();
        _ = new Bag { 1, 2 };
        Console.WriteLine();
    }
}

static class Extensions
{
    public static void Add(this IAppend bag, object item)
    {
        bag.Append(item);
        Console.Write(item);
    }
}
"#,
        "none\nhandled\n12\n",
    );
}

/// `[0] = { B = 1 }` in an object initializer initializes the element the
/// indexer reads.
#[test]
fn an_indexer_initializer_can_initialize_the_element() {
    check(
        "RefNestedIndexerInitializer",
        r#"
using System;

class C
{
    C[] items;
    int b;

    C() { }
    C(bool made) { items = new C[2] { new C(), new C() }; }

    static void Main()
    {
        var c = new C(true) { items = { [0] = { b = 1 }, [1] = { b = 2 } } };
        Console.WriteLine(c.items[0].b + " " + c.items[1].b);
    }
}
"#,
        "1 2\n",
    );
}

/// A variable a `while` condition declares is fresh each time round, and a
/// closure over it sees that iteration's value — in an async method too.
#[test]
fn while_condition_variables_are_per_iteration() {
    check(
        "RefWhileConditionCapture",
        r#"
using System;
using System.Collections.Generic;
using System.Threading.Tasks;

static class Program
{
    static async Task<int> Later(int x) { await Task.Yield(); return x; }

    static async Task RunAsync()
    {
        var actions = new List<Func<int>>();
        int i = 0;
        while (i is int j && i++ < 3)
        {
            await Later(j);
            actions.Add(() => j * 10);
        }
        foreach (var action in actions) Console.Write(action() + " ");
        Console.WriteLine();
    }

    static void Main()
    {
        var actions = new List<Action>();
        var strings = new List<string> { "one", "two", "three" };
        int i = 0;
        while (i is int j && i++ < 3)
            actions.Add(() => Console.Write(strings[j] + " "));
        foreach (var action in actions) action();
        Console.WriteLine();
        RunAsync().Wait();
    }
}
"#,
        "one two three \n0 10 20 \n",
    );
}

/// `new()` in an interpolation hole or an array size, `field` in an
/// expression-bodied property, and a floating zero given to an enum.
#[test]
fn target_typed_new_in_holes_field_in_arrows_and_enum_zeros() {
    check(
        "RefTargetTypedHoles",
        r#"
using System;

class C
{
    enum Gender : byte { Male = 2 }

    public object P => field ??= "made";

    static void Main()
    {
        Console.WriteLine($"({new()})".Length > 2);
        var a = new int[new()];
        Console.WriteLine(a.Length);
        var c = new C();
        Console.WriteLine(c.P + " " + ReferenceEquals(c.P, c.P));
        Gender g = 0.0;
        Console.WriteLine(g);
    }
}
"#,
        "True\n0\nmade True\n0\n",
    );
}

/// An override's type parameter has the overridden method's constraints,
/// put into the override's terms: `where S : T` in `A<T>` is `where S : P`
/// in `B : A<P>`.
#[test]
fn an_override_inherits_constraints_through_its_base_arguments() {
    check(
        "RefInheritedConstraintTerms",
        r#"
using System;

abstract class A<T>
{
    public abstract void Goo<S>() where S : T, new();
}

class P
{
    public int X;
}

class B : A<P>
{
    public override void Goo<S>()
    {
        var s = new S();
        s.X = 5;
        Console.WriteLine(s.X);
    }

    static void Main() => new B().Goo<P>();
}
"#,
        "5\n",
    );
}

#[test]
fn an_iterator_runs_its_finally_however_the_walk_ends() {
    check(
        "RefIteratorFinally",
        r#"
using System;
using System.Collections.Generic;
using System.Linq;

sealed class Noisy : IDisposable
{
    readonly string _name;
    public Noisy(string name) { _name = name; Console.WriteLine("open " + _name); }
    public void Dispose() { Console.WriteLine("close " + _name); }
}

class Program
{
    static IEnumerable<int> Guarded(int count)
    {
        Console.WriteLine("start");
        try
        {
            using (var outer = new Noisy("outer"))
            {
                for (int i = 0; i < count; i++)
                {
                    using var inner = new Noisy("inner" + i);
                    yield return i;
                }
            }
            yield return 99;
        }
        finally
        {
            Console.WriteLine("finally");
        }
        Console.WriteLine("end");
    }

    static IEnumerable<T> Each<T>(List<T> items)
    {
        foreach (var item in items)
        {
            yield return item;
        }
        lock (items)
        {
            yield return items[0];
        }
    }

    static void Main()
    {
        foreach (var n in Guarded(2)) { Console.WriteLine("got " + n); }
        Console.WriteLine("--");
        foreach (var n in Guarded(2)) { Console.WriteLine("got " + n); if (n == 1) break; }
        Console.WriteLine("--");
        Console.WriteLine(string.Join(",", Each(new List<string> { "a", "b" })));
        Console.WriteLine(Each(new List<int> { 5, 6 }).First());
    }
}
"#,
        "start\nopen outer\nopen inner0\ngot 0\nclose inner0\nopen inner1\ngot 1\nclose inner1\nclose outer\ngot 99\nfinally\nend\n--\nstart\nopen outer\nopen inner0\ngot 0\nclose inner0\nopen inner1\ngot 1\nclose inner1\nclose outer\nfinally\n--\na,b,a\n5\n",
    );
}

#[test]
fn a_lambda_inside_a_state_machine_is_a_method_of_it() {
    check(
        "RefMachineLambdas",
        r#"
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;

class Counter
{
    int _base = 100;

    public async Task<int> SumAsync(int[] values)
    {
        int seen = 0;
        Func<int, int> weigh = v => v * 2 + _base;
        foreach (var value in values)
        {
            await Task.Yield();
            seen += weigh(value);
        }
        int Local(int x) => x + seen;
        return await Task.FromResult(Local(1));
    }

    public IEnumerable<string> Names(List<string> raw)
    {
        var prefix = "n:";
        foreach (var name in raw.Where(n => n.Length > 1).Select(n => prefix + n))
        {
            yield return name;
        }
        Func<string> last = () => prefix + _base;
        yield return last();
    }
}

class Box<T>
{
    public T Value;
    public Box(T value) { Value = value; }
    public async Task<List<T>> RepeatAsync(int times)
    {
        var made = new List<T>();
        Action add = () => made.Add(Value);
        for (int i = 0; i < times; i++)
        {
            await Task.Yield();
            add();
        }
        return made;
    }
}

class Program
{
    static void Main() => Run().GetAwaiter().GetResult();

    static async Task Run()
    {
        var counter = new Counter();
        Console.WriteLine(await counter.SumAsync(new[] { 1, 2, 3 }));
        Console.WriteLine(string.Join(",", counter.Names(new List<string> { "a", "bb", "ccc" })));
        Console.WriteLine(string.Join(",", await new Box<string>("x").RepeatAsync(3)));
    }
}
"#,
        "313\nn:bb,n:ccc,n:100\nx,x,x\n",
    );
}

#[test]
fn unsafe_code_pins_points_and_allocates_on_the_stack() {
    check(
        "RefUnsafe",
        r#"
using System;
using System.Runtime.InteropServices;

struct Pair { public int A; public int B; }

unsafe class Program
{
    static int Sum(int* values, int count)
    {
        int total = 0;
        for (int* p = values; p < values + count; p++)
        {
            total += *p;
        }
        return total;
    }

    static void Fill(byte* bytes, int count)
    {
        for (int i = 0; i < count; i++)
        {
            bytes[i] = (byte)(i * 3);
        }
    }

    static ulong Read(ulong* words) => words[1] + *words;

    static void Main()
    {
        int[] numbers = { 1, 2, 3, 4 };
        fixed (int* p = numbers)
        {
            Console.WriteLine(Sum(p, numbers.Length));
            Console.WriteLine(p[2]);
            p[3] = 40;
            *p += 10;
        }
        Console.WriteLine(numbers[0] + "," + numbers[3]);

        string text = "hello";
        fixed (char* c = text)
        {
            Console.WriteLine(c[1]);
            Console.WriteLine((int)(c + 4 - c));
        }

        var pair = new Pair { A = 7, B = 9 };
        fixed (int* a = &pair.B)
        {
            *a = 11;
        }
        Console.WriteLine(pair.B);

        ReadOnlySpan<char> slice = text.AsSpan(1, 3);
        fixed (char* s = slice)
        {
            Console.WriteLine(new string(s, 0, 3));
        }

        byte* buffer = stackalloc byte[6];
        Fill(buffer, 6);
        Console.WriteLine(buffer[5]);
        Span<int> span = stackalloc int[] { 5, 6, 7 };
        Console.WriteLine(span[1] + span.Length);
        ulong* words = stackalloc ulong[2];
        words[0] = 100;
        words[1] = 23;
        Console.WriteLine(Read(words));
        byte* bytes = (byte*)words;
        Console.WriteLine(bytes[0]);
        Console.WriteLine(sizeof(Pair));
        int local = 5;
        int* address = &local;
        *address = 6;
        Console.WriteLine(local);
        int[] empty = new int[0];
        fixed (int* e = empty)
        {
            Console.WriteLine(e == null);
        }
    }
}
"#,
        "10\n3\n11,40\ne\n4\n11\nell\n15\n9\n123\n100\n8\n6\nTrue\n",
    );
}

#[test]
fn a_with_expression_against_the_real_framework() {
    check(
        "with_expression",
        r#"
using System;

struct Info
{
    public string Name;
    public int Count { get; set; }
}

record Builder(string Source)
{
    public int Steps { get; init; }
    public string Tag = "t";
}

record Derived(string Source, bool Flag) : Builder(Source);

static class Program
{
    static void Main()
    {
        var info = new Info { Name = "a", Count = 1 };
        var changed = info with { Count = 5 };
        Console.WriteLine(info.Name + info.Count + changed.Name + changed.Count);
        var pair = (Type: "int", FromFunctionType: false);
        var next = pair with { FromFunctionType = true };
        Console.WriteLine(pair.FromFunctionType + " " + next.Type + next.FromFunctionType);
        var builder = new Builder("src") { Steps = 2 };
        var copy = builder with { Steps = 7 };
        Console.WriteLine(builder.Steps + " " + copy.Source + copy.Steps + copy.Tag);
        Console.WriteLine(ReferenceEquals(builder, copy));
        Builder derived = new Derived("d", true);
        var again = derived with { Steps = 9 };
        Console.WriteLine(again.GetType().Name);
        Console.WriteLine(again is Derived d ? d.Flag + " " + d.Steps + d.Source + d.Tag : "wrong");
    }
}
"#,
        "a1a5\nFalse intTrue\n2 src7t\nFalse\nDerived\nTrue 9dt\n",
    );
}

/// A record's members have the shape Roslyn gives them: `ToString` prints
/// through `PrintMembers` (base record first, public fields too), equality
/// compares the `EqualityContract` and every field, a derived record
/// overrides the base's `Equals(Base)`, the record is an `IEquatable<R>`,
/// and a member the source wrote — a `ToString`, a copy constructor, an
/// `Equals(ref R)` beside the language's — is left alone or used.
#[test]
fn records_get_roslyns_members_against_the_real_framework() {
    check(
        "roslyn_records",
        r#"
using System;

record A(int X)
{
    public int Field = 5;
    private int _hidden = 1;
    public virtual bool Equals(ref A other) => throw null;
}
record B(int X, int Y) : A(X);
record C
{
    private static int _next;
    private int _id = _next++;
}
record D(int X)
{
    public override string ToString() => "D" + X;
    protected D(D other) { X = other.X + 100; }
}
record struct S(int X, string Name);

class Program
{
    static void Main()
    {
        Console.WriteLine(new A(1));
        Console.WriteLine(new B(1, 2));
        Console.WriteLine(new A(1) == new A(1));
        Console.WriteLine(new A(1).Equals((A)new B(1, 2)));
        Console.WriteLine(((A)new B(1, 2)).Equals(new A(1)));
        Console.WriteLine(new B(1, 2) == new B(1, 2));
        Console.WriteLine(new C() == new C());
        IEquatable<A> equatable = new A(3);
        Console.WriteLine(equatable.Equals(new A(3)));
        Console.WriteLine(new D(1) with { });
        Console.WriteLine(new S(4, "four"));
        Console.WriteLine(new S(4, "four") == new S(4, "four"));
        Console.Write("{braces}");
        Console.WriteLine();
    }
}
"#,
        "A { X = 1, Field = 5 }\nB { X = 1, Field = 5, Y = 2 }\nTrue\nFalse\nFalse\nTrue\nFalse\nTrue\nD101\nS { X = 4, Name = four }\nTrue\n{braces}\n",
    );
}

/// A struct's `: this()` reaching the constructor nobody wrote runs the
/// field initializers after zeroing; a lambda in a field initializer reads
/// the primary constructor's parameter it closes over.
#[test]
fn constructors_run_initializers_where_csharp_says_against_the_real_framework() {
    check(
        "constructor_initializers",
        r#"
using System;

struct S
{
    int x = 1;
    int y;
    public S(int y) : this() { this.y = y; }
    public override string ToString() => (x, y).ToString();
}
class C(int p)
{
    Func<int> Z = () => p + 1;
    public int Get() => Z();
}
class Program
{
    static void Main()
    {
        Console.WriteLine(new S(2));
        Console.WriteLine(new S());
        Console.WriteLine(new C(41).Get());
    }
}
"#,
        "(1, 2)\n(0, 0)\n42\n",
    );
}

/// `params` collections (C# 13) take their arguments one by one into the
/// collection, and an expanded candidate is compared element by element; a
/// generic attribute names its construction's constructor; the declaring
/// part of a partial method carries attributes too; `typeof(Attr<>)` is the
/// definition; `[CallerMemberName]` on an attribute of a type is the default.
#[test]
fn params_collections_and_attributes_against_the_real_framework() {
    check(
        "params_collections_attributes",
        r#"
using System;
using System.Collections.Generic;
using System.Reflection;
using System.Runtime.CompilerServices;

class Attr<T> : Attribute { public Attr(T value) { Console.WriteLine("Attr " + value); } }
class A : Attribute { }
class Caller : Attribute { public Caller([CallerMemberName] string name = "none") { Console.WriteLine(name); } }

[Attr<string>("a")]
[Caller]
partial class Program
{
    static void F(params List<int> xs) { Console.WriteLine("ints " + xs.Count); }
    static void F(params List<byte> xs) { Console.WriteLine("bytes " + xs.Count); }
    static void E(params IEnumerable<string> xs) { Console.WriteLine(string.Join("+", xs)); }
    static void S(params ReadOnlySpan<int> xs) { Console.WriteLine(xs.Length); }

    [A]
    static partial void Goo();
    static partial void Goo() { }

    static void Main()
    {
        F((byte)1, (byte)2);
        F(1, 2, 3);
        E("x", "y");
        E();
        S(1, 2, 3, 4);
        typeof(Program).GetCustomAttributes(false);
        Console.WriteLine(((Action)Goo).Method.GetCustomAttributesData().Count);
        Console.WriteLine(typeof(Attr<>).IsGenericTypeDefinition);
        Console.Write("{0}");
        Console.WriteLine();
    }
}
"#,
        "bytes 2\nints 3\nx+y\n\n4\nAttr a\nnone\n1\nTrue\n{0}\n",
    );
}

/// Target-typed `new()` takes its type wherever one is given: in an
/// interpolation hole, an array size, a constant pattern, an indexer key of
/// an object initializer, and as a `T` with an initializer.
#[test]
fn target_typed_new_everywhere_against_the_real_framework() {
    check(
        "target_typed_new",
        r#"
using System;
using System.Collections.Generic;

class C
{
    public int i;
    static void M<T>() where T : C, new()
    {
        T t = new() { i = 43 };
        Console.WriteLine(t.i + new T { i = 1 }.i);
    }
    static void Main()
    {
        Console.WriteLine($"({new()})");
        var a = new int[new()];
        Console.WriteLine(a.Length);
        int x = 0;
        Console.WriteLine(x is new());
        Dictionary<C, int> d = new() { [new() { i = 3 }] = 7 };
        foreach (var k in d.Keys) Console.WriteLine(k.i);
        M<C>();
    }
}
"#,
        "(System.Object)\n0\nTrue\n3\n44\n",
    );
}

/// `field` in an expression-bodied property is its backing field, and an
/// interpolation's alignment is a constant expression folded into the
/// format.
#[test]
fn field_in_an_arrow_body_and_a_folded_alignment_against_the_real_framework() {
    check(
        "field_arrow_alignment",
        r#"
using System;
class C
{
    public object P => field = 1;
    public static object Q { get => field ??= 2; }
}
class Program
{
    static void Main()
    {
        Console.WriteLine((new C().P, C.Q));
        Console.WriteLine($"X = { 123 , -(3+4) }.");
    }
}
"#,
        "(1, 2)\nX = 123    .\n",
    );
}

/// Extension blocks (C# 14): instance properties with accessor bodies read
/// and written — compound, increment through a user-defined `++` —
/// indexers, static properties and methods reached through the type,
/// operators, a generic block's members on a type parameter, a delegate
/// property invoked, and an extension `GetEnumerator` with an optional
/// parameter.
#[test]
fn extension_blocks_against_the_real_framework() {
    check(
        "extension_blocks",
        r#"
using System;

public class C { public int F; }
public struct S2
{
    public int V;
    public static S2 operator ++(S2 x) => new S2 { V = x.V + 1 };
}
public class Bag
{
    public sealed class Enumerator
    {
        public Enumerator(int start) => Current = start;
        public int Current { get; private set; }
        public bool MoveNext() => Current++ != 3;
    }
}

static class E
{
    extension(C c)
    {
        public int P
        {
            get { Console.Write("get "); return c.F; }
            set { Console.Write("set "); c.F = value; }
        }
        public int this[int i] { get => c.F + i; set => c.F = value - i; }
        public S2 Step { get => new S2 { V = c.F }; set => c.F = value.V; }
        public Action Hello => () => Console.WriteLine("hello");
        public static C Make() => new C { F = 1 };
        public static int Count => 3;
    }
    extension(C)
    {
        public static C operator +(C a, C b) => new C { F = a.F + b.F };
    }
    extension<T>(T x)
    {
        public string Name => typeof(T).Name;
    }
    extension(Bag bag)
    {
        public Bag.Enumerator GetEnumerator(int start = 1) => new Bag.Enumerator(start);
    }
}

class Program
{
    static void Main()
    {
        var c = C.Make();
        c.P += 10;
        Console.WriteLine(c.P);
        c[2] = 7;
        Console.WriteLine(c[1]);
        c.Step++;
        Console.WriteLine(c.F);
        Console.WriteLine((c + c).F + C.Count);
        Console.WriteLine(42.Name + " " + c.Name);
        Console.WriteLine(c is { Name: "C" } && new S2() is { Name: "S2" });
        c.Hello();
        foreach (var i in new Bag()) Console.Write(i);
        Console.WriteLine();
    }
}
"#,
        "get set get 11\n6\n6\n15\nInt32 C\nTrue\nhello\n23\n",
    );
}

/// A field-like event is invoked by its bare name; `case C():` takes a `C`
/// apart rather than calling it; a collection initializer reaches an
/// extension `Add`.
#[test]
fn events_case_patterns_and_extension_adds_against_the_real_framework() {
    check(
        "events_case_extension_add",
        r#"
using System;
using System.Collections;
using System.Collections.Generic;

record C()
{
    public void Deconstruct() { }
}
class Bag : IEnumerable
{
    public List<int> Items = new();
    public IEnumerator GetEnumerator() => Items.GetEnumerator();
}
static class Extensions
{
    public static void Add(this Bag bag, int item) => bag.Items.Add(item * 10);
}
class Program
{
    event Func<string> E;

    void Fire() => Console.WriteLine(E != null ? E() : "none");

    static void Main()
    {
        var p = new Program();
        p.Fire();
        p.E += () => "fired";
        p.Fire();
        switch (new C())
        {
            case C():
                Console.WriteLine("taken apart");
                break;
        }
        var bag = new Bag { 1, 2 };
        Console.WriteLine(string.Join(",", bag.Items));
    }
}
"#,
        "none\nfired\ntaken apart\n10,20\n",
    );
}

/// A lambda among a primary constructor's base arguments closes over the
/// parameter before the base constructor runs; a parameter a lambda in
/// another part of a partial class reads is captured all the same.
#[test]
fn primary_constructor_captures_across_parts_against_the_real_framework() {
    check(
        "primary_constructor_captures",
        r#"
using System;

class Base
{
    public Base(Func<int> x) { Console.WriteLine(x()); }
}
class C(int X) : Base(() => X + 1);

partial class D
{
    public Func<int> F = () => p++;
}
partial class D(int p)
{
    public int Now => p;
}

class Program
{
    static void Main()
    {
        _ = new C(41);
        var d = new D(5);
        Console.WriteLine(d.F() + d.F() + d.Now);
    }
}
"#,
        "42\n18\n",
    );
}

/// An anonymous type keeps its values in readonly `<A>i__Field` fields, is
/// equal field by field, and hashes as Roslyn does; `new { }` is allowed.
#[test]
fn anonymous_types_get_roslyns_fields_and_equality_against_the_real_framework() {
    check(
        "anonymous_fields_and_equality",
        r#"
using System;
using System.Reflection;

class Program
{
    static void Main()
    {
        var a = new { A = 1, B = "x" };
        var field = a.GetType().GetFields(BindingFlags.NonPublic | BindingFlags.Instance)[0];
        Console.WriteLine(field.Name + " " + field.IsInitOnly);
        Console.WriteLine(a.Equals(new { A = 1, B = "x" }) + " " + a.Equals(new { A = 2, B = "x" }));
        Console.WriteLine(a.GetHashCode() == new { A = 1, B = "x" }.GetHashCode());
        Console.WriteLine(new { }.GetHashCode());
    }
}
"#,
        "<A>i__Field True\nTrue False\nTrue\n0\n",
    );
}

/// Lambdas given for a `params` array are its elements, for a generic
/// method or a constructor alike, and of two constructors that fit equally
/// the one whose declared parameter mentions no type parameter wins.
#[test]
fn lambdas_in_a_params_array_against_the_real_framework() {
    check(
        "params_lambdas",
        r#"
using System;

class Bar { public Wrapper<int> Value => new Wrapper<int>(); }
struct Wrapper<T> { }
class C
{
    public void Method<S>(params Func<Bar, S>[] projections) => Console.Write(1);
    public void Method<S>(params Func<Bar, Wrapper<S>>[] projections) => Console.Write(2);
}
class D<S>
{
    public D(params Func<Bar, S>[] projections) => Console.Write(projections.Length);
    public D(params Func<Bar, Wrapper<int>>[] projections) => Console.Write(9);
}
class E
{
    public E(params Func<int, int>[] steps) => Console.Write(steps[1](steps[0](1)));
}
class Program
{
    static void Main()
    {
        new C().Method(x => x.Value);
        new D<Wrapper<int>>(x => x.Value);
        new D<int>(x => 1, x => 2);
        new E(x => x + 1, x => x * 10);
        Console.WriteLine();
    }
}
"#,
        "29220\n",
    );
}

/// The two parts of a partial property or indexer are one member, declared
/// by the implementing part and matched by signature; an indexer's `params`
/// indices are packed into its array or collection.
#[test]
fn partial_properties_and_params_indexers_against_the_real_framework() {
    check(
        "partial_properties_params_indexers",
        r#"
using System;
using System.Collections.Generic;

partial class C
{
    public partial int P { get; set; }
    public partial int P { get => 5; set { Console.Write(value); } }

    public partial int this[int x, int y] { get; }
    public partial int this[int x, int y = 1] { get => x + y; }
    public partial int this[string x, int y] { get; }
    public partial int this[string x, int y] { get => y * 10; }

    public int this[params string[] words] => words.Length;
    public int this[params IEnumerable<bool> flags]
    {
        get { foreach (var flag in flags) Console.Write(flag); return 0; }
    }

    static void Main()
    {
        var c = new C();
        Console.Write(c.P);
        c.P = 3;
        Console.Write(c[1, 2]);
        Console.Write(c["a", 4]);
        Console.Write(c["a", "b", "c"]);
        _ = c[true, false];
        Console.WriteLine(typeof(C).GetProperties().Length);
    }
}
"#,
        "533403TrueFalse5\n",
    );
}

/// An override that declares only a setter inherits the base's getter, and
/// a left-out index takes the default of the accessor that is called.
#[test]
fn an_override_inherits_the_accessor_it_leaves_out_against_the_real_framework() {
    check(
        "override_inherits_accessor",
        r#"
using System;

class Base
{
    public virtual int this[int x, int y = 1]
    {
        get { Console.Write("get" + y + " "); return y; }
        set { Console.Write("set" + y + " "); }
    }
    public virtual int P { get => 7; set { } }
}
class Override : Base
{
    public override int this[int x, int y = 2]
    {
        set { Console.Write("oset" + y + " "); }
    }
    public override int P { set { Console.Write("P" + value + " "); } }
}
class Program
{
    static void Main()
    {
        var o = new Override();
        _ = o[0];
        o[0] = 0;
        o[0] += 0;
        o.P = o.P;
        Console.WriteLine();
    }
}
"#,
        "get1 oset2 get1 oset1 P7 \n",
    );
}

/// An interpolated string reaches a user-defined conversion or operator
/// taking an `IFormattable` or a `FormattableString`, in a tuple comparison
/// too; a bare `default` in a hole is an object's.
#[test]
fn interpolated_strings_reach_user_defined_operators_against_the_real_framework() {
    check(
        "interpolated_user_operators",
        r#"
using System;

class Wrapped
{
    FormattableString inner;
    public static implicit operator Wrapped(FormattableString inner) => new Wrapped { inner = inner };
    public override string ToString() => "W:" + inner.Format;
}
class K
{
    public static bool operator ==(K k, IFormattable a) => a.ToString() == "frog";
    public static bool operator !=(K k, IFormattable a) => false;
    public override bool Equals(object other) => false;
    public override int GetHashCode() => 1;
}
class Program
{
    static void Main()
    {
        Console.WriteLine((Wrapped)$"dog");
        K k = null;
        Console.WriteLine((k == $"frog") + " " + ((k, 1) == ($"frog", 1)));
        Console.WriteLine($"[{default}]");
    }
}
"#,
        "W:dog\nTrue True\n[]\n",
    );
}

/// A partial method is `async` where its implementing part says so, and
/// can be the entry point.
#[test]
fn an_async_partial_method_against_the_real_framework() {
    check(
        "async_partial_method",
        r#"
using System;
using System.Threading.Tasks;

partial class C
{
    private static partial Task<int> M1();
    private static async partial Task<int> M1() { await Task.Yield(); return 1; }

    public static partial Task Main();
    public static async partial Task Main()
    {
        Console.WriteLine(await M1());
    }
}
"#,
        "1\n",
    );
}

/// An extension method's receiver converts only by identity, reference or
/// boxing; the extension methods of the enclosing namespace are looked at
/// before the imported ones; `foreach` over an `int?` finds a
/// `GetEnumerator(this int?)`.
#[test]
fn extension_methods_by_scope_and_receiver_conversion_against_the_real_framework() {
    check(
        "extension_scope_receiver",
        r#"
using System;
using N;

static class Program
{
    static void Main()
    {
        0.Goo();
        DayOfWeek.Monday.Goo();
        "".Bar(1);
        foreach (var i in (int?)null)
        {
            Console.Write(i);
        }
        Console.WriteLine();
    }

    static void Goo(this long x) => Console.Write("long ");
    static void Goo(this object x) => Console.Write("object ");
    public static void Bar(this string x, object y) => Console.Write("outer ");
}

namespace N
{
    static class C
    {
        public static void Bar(this string x, int y) => Console.Write("imported ");
    }
}

public sealed class Counter
{
    public int Current { get; private set; }
    public bool MoveNext() => Current++ != 3;
}
public static class Extensions
{
    public static Counter GetEnumerator(this int? self) => new Counter();
}
"#,
        "object object outer 123\n",
    );
}

/// `[Optional]` and `[DefaultParameterValue]` make a parameter optional,
/// an `[Optional] object` left out is `Missing.Value`, `default(int)` is a
/// constant an attribute may take, a `decimal?` takes an `int`, and an
/// extension `GetEnumerator` quotes the collection for a
/// `[CallerArgumentExpression]`.
#[test]
fn optional_parameters_and_constant_defaults_against_the_real_framework() {
    check(
        "optional_parameters_constant_defaults",
        r#"
using System;
using System.Collections;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

public class NumberAttribute : Attribute
{
    public NumberAttribute(int value) { Console.Write("attr" + value + " "); }
}

public static class Extensions
{
    public static IEnumerator GetEnumerator(this IEnumerator e, [CallerArgumentExpression("e")] string text = "none")
    {
        Console.Write(text + " ");
        return e;
    }
}

[Number(default(int))]
class Program
{
    static void Optional([Optional] int x, [Optional] object o, [Optional, DefaultParameterValue(nameof(Optional))] string s)
    {
        Console.Write(x + " " + (o == Missing.Value) + " " + s + " ");
    }
    static void Money(decimal? amount = 7) => Console.Write(amount + " ");

    static void Main()
    {
        Optional();
        decimal? five = 5;
        Money(five);
        Money();
        typeof(Program).GetCustomAttribute(typeof(NumberAttribute));
        var items = new[] { "a" }.GetEnumerator();
        foreach (var item in items) { }
        var p = typeof(Program).GetMethod("Optional", BindingFlags.NonPublic | BindingFlags.Static).GetParameters();
        Console.WriteLine(p[0].IsOptional + " " + p[0].HasDefaultValue + " " + p[2].DefaultValue);
    }
}
"#,
        "0 True Optional 5 7 attr0 items True False Optional\n",
    );
}

/// An extension block's `GetPinnableReference` is what `fixed` pins, and
/// its property is what an object initializer sets.
#[test]
fn fixed_and_initializers_reach_extension_members_against_the_real_framework() {
    check(
        "fixed_initializer_extensions",
        r#"
unsafe class Program
{
    static void Main()
    {
        fixed (int* p = new Fixable())
        {
            System.Console.Write(p[1] + " ");
        }
        _ = new S { Prop = 5 };
        System.Console.WriteLine();
    }
}

class Fixable
{
    public ref int GetPinnableReference(int notApplicable) => throw null;
}

public struct S { public int F; }

static class E
{
    static int[] numbers = { 1, 2, 3 };
    extension(Fixable f)
    {
        public ref int GetPinnableReference() => ref numbers[0];
    }
    extension(S s)
    {
        public int Prop { set { System.Console.Write("set " + value); } }
    }
}
"#,
        "2 set 5\n",
    );
}

/// A captured primary constructor parameter is its field everywhere, the
/// initializers and the base arguments' lambdas included; `(_, _) => _`
/// reads the `_` around it; a parameter called `nameof` is called; and a
/// candidate that needs no default beats a non-generic one that does.
#[test]
fn primary_constructor_fields_discards_and_tie_breaks_against_the_real_framework() {
    check(
        "primary_fields_discards_tie_breaks",
        r#"
using System;

class Base
{
    public Func<int> Z;
    public Base(Func<int> z) { Z = z; }
}
class C(int p) : Base(() => p)
{
    readonly int y = Write(out p);
    public int Bump() => ++p;
    static int Write(out int x) { x = 10; return 0; }
}
class D(int _)
{
    public Func<int, int, int> Pick() => (_, _) => _;
}
class N(Func<int, int> nameof, int q)
{
    public int Call() => nameof(q);
}
class Color
{
    public string M(string x, int y = 0) => "instance";
    public static string M<T>(T x) => "static";
}
class Program
{
    static void Main()
    {
        var c = new C(1);
        Console.Write(c.Bump() + " " + c.Z() + " ");
        Console.Write(new D(20).Pick()(-2, -3) + " ");
        Console.Write(new N(x => x * 2, 21).Call() + " ");
        Console.WriteLine(new Holder(new Color()).Which());
    }
}
struct Holder(Color Color)
{
    public string Which() => Color.M("a");
}
"#,
        "11 11 20 42 static\n",
    );
}

/// An interface's event is two abstract accessors, implemented by an event
/// with accessor blocks, by a field-like event, or explicitly.
#[test]
fn events_declared_by_interfaces_against_the_real_framework() {
    check(
        "interface_events",
        r#"
using System;

interface I
{
    event EventHandler E;
}
class Blocks : I
{
    public event EventHandler E
    {
        add { Console.Write("add "); }
        remove { Console.Write("remove "); }
    }
}
class FieldLike : I
{
    public event EventHandler E;
    public void Raise() => E?.Invoke(this, EventArgs.Empty);
}
class Explicit : I
{
    event EventHandler I.E
    {
        add { Console.Write("explicit-add "); }
        remove { Console.Write("explicit-remove "); }
    }
}
class Program
{
    static void Main()
    {
        I blocks = new Blocks();
        blocks.E += null;
        blocks.E -= null;
        var fieldLike = new FieldLike();
        ((I)fieldLike).E += (sender, args) => Console.Write("raised ");
        fieldLike.Raise();
        I explicitly = new Explicit();
        explicitly.E += null;
        explicitly.E -= null;
        Console.WriteLine();
    }
}
"#,
        "add remove raised explicit-add explicit-remove \n",
    );
}

/// A named argument rules out the overloads without that parameter where
/// it stands; `case new():` and `goto case new();` are the switch type's
/// zero.
#[test]
fn named_arguments_pick_overloads_and_new_in_case_labels_against_the_real_framework() {
    check(
        "named_overloads_case_new",
        r#"
using System;

class C
{
    public C(object c, object o) => Console.Write("object ");
    public C(int i, object o) => Console.Write("int ");
    static void M(object c, object o) => Console.Write("M-object ");
    static void M(int i, object o) => Console.Write("M-int ");

    static int Get(int i)
    {
        switch (i)
        {
            case new():
                return 1;
            case 1:
                goto case new();
            default:
                return 2;
        }
    }

    static void Main()
    {
        C c = new(c: new(), 2);
        new C(c: 5, 2);
        M(c: 5, 2);
        Console.WriteLine("" + Get(0) + Get(1) + Get(2));
    }
}
"#,
        "object object M-object 112\n",
    );
}

/// An explicit implementation is named for its interface as Roslyn writes
/// it, and a class that lists an interface extending one its base
/// implements implements that one anew.
#[test]
fn explicit_names_and_reimplemented_interfaces_against_the_real_framework() {
    check(
        "explicit_names_reimplementation",
        r#"
using System;

namespace N
{
    interface I<T> { void Goo(); int P { get; } }
}
interface I1 { void Go(); }
interface I2 : I1 { }
class X : I1
{
    void I1.Go() => Console.Write("X ");
}
class Y : X, I2
{
    public virtual void Go() => Console.Write("Y ");
}
class C : N.I<int[][,]>
{
    void N.I<int[][,]>.Goo() { }
    int N.I<int[][,]>.P => 1;
    static void Main()
    {
        N.I<int[][,]> x = new C();
        Action a = x.Goo;
        Console.Write(a.Method.Name + " ");
        Console.Write(typeof(C).GetProperties(System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Instance)[0].Name + " ");
        I2 y = new Y();
        y.Go();
        Console.WriteLine();
    }
}
"#,
        "N.I<System.Int32[,][]>.Goo N.I<System.Int32[,][]>.P Y \n",
    );
}

/// `fixed` over a type parameter pins what its constraint's
/// `GetPinnableReference` returns, called on the variable itself.
#[test]
fn fixed_over_a_type_parameter_against_the_real_framework() {
    check(
        "fixed_type_parameter",
        r#"
unsafe class C
{
    static void Main()
    {
        var a = new FixableClass();
        Test(ref a);
        System.Console.WriteLine(a.x);
    }

    static void Test<T>(ref T arg) where T : IFixable
    {
        fixed (int* p = arg)
        {
            System.Console.Write(p[1]);
        }
    }
}

interface IFixable
{
    ref int GetPinnableReference();
}

class FixableClass : IFixable
{
    public int x;
    static int[] numbers = { 1, 2, 3 };
    public ref int GetPinnableReference()
    {
        x = 123;
        return ref numbers[0];
    }
}
"#,
        "2123\n",
    );
}

/// A type nested in an interface is public unless it says otherwise, and
/// `typeof(void)` is `System.Void`.
#[test]
fn interface_nested_types_and_typeof_void_against_the_real_framework() {
    check(
        "interface_nested_typeof_void",
        r#"
using System;

interface I
{
    class Nested { }
}
class Program
{
    static void Main()
    {
        Console.WriteLine(typeof(I.Nested).IsNestedPublic + " " + typeof(void).FullName);
    }
}
"#,
        "True System.Void\n",
    );
}

#[test]
fn a_static_member_of_a_generic_base_against_the_real_framework() {
    check(
        "static_through_generic_base",
        r#"
using System;
using System.Collections.Generic;

abstract class Decoder<TModule, TSymbol>
{
    internal static void Counts(TModule module, out int parameters, out int types)
    {
        parameters = module.ToString().Length;
        types = 2;
    }
}

class Decoder : Decoder<string, object>
{
}

abstract class Manager<TValue>
{
    protected static bool SameLength(string left, string right) => left.Length == right.Length;

    protected static TValue Find(Dictionary<string, TValue> map, string key, Func<string, string, bool> compare)
    {
        foreach (var pair in map)
        {
            if (compare(pair.Key, key))
            {
                return pair.Value;
            }
        }
        return default;
    }
}

sealed class Manager : Manager<int>
{
    public int Lookup(Dictionary<string, int> map, string key) => Find(map, key, SameLength);
}

class Extensions<TExtension>
{
    private Func<string, Extensions<TExtension>, TExtension> _factory;

    private static TExtension Create(string language, Extensions<TExtension> owner) => owner.Make(language);

    protected virtual TExtension Make(string language) => default;

    public TExtension Get(string language)
    {
        _factory = Create;
        return _factory(language, this);
    }
}

class Lengths : Extensions<int>
{
    protected override int Make(string language) => language.Length;
}

struct Annotated
{
    public string Name;

    public static bool operator ==(Annotated? x, Annotated? y) =>
        x.HasValue == y.HasValue && (!x.HasValue || x.GetValueOrDefault().Name == y.GetValueOrDefault().Name);

    public static bool operator !=(Annotated? x, Annotated? y) => !(x == y);

    public override bool Equals(object o) => false;

    public override int GetHashCode() => 0;
}

readonly record struct Entry<T>(T Item, int State);

readonly struct Dest
{
    public readonly string Name;
    public readonly int Level;

    public Dest(string name, int level)
    {
        Name = name;
        Level = level;
    }

    public override string ToString() => (Name, Level).ToString();
}

enum Kind { A = 1, B, C }

static class Kinds
{
    private const Kind @base = Kind.C + 1;
    public const Kind Arity = @base + 0;
    public const Kind Other = @base + 1;
}

static class Program
{
    static void Main()
    {
        Decoder.Counts("module", out var parameters, out var types);
        Console.WriteLine(parameters + types);
        Console.WriteLine(new Manager().Lookup(new Dictionary<string, int> { ["abc"] = 7 }, "xyz"));
        Console.WriteLine(new Lengths().Get("seven"));
        Annotated a = new Annotated { Name = "x" };
        Annotated b = new Annotated { Name = "x" };
        Annotated? none = null;
        Console.WriteLine(a == b);
        Console.WriteLine(a != b);
        Console.WriteLine(none == a);
        var (item, state) = new Entry<string>("i", 3);
        Console.WriteLine(item + state);
        Console.WriteLine(new Dest("p", 2));
        Console.WriteLine((int)Kinds.Arity + " " + (int)Kinds.Other);
    }
}
"#,
        "8\n7\n5\nTrue\nFalse\nFalse\ni3\n(p, 2)\n4 5\n",
    );
}

#[test]
fn a_source_collection_builder_a_table_initializer_and_a_list_case_label() {
    check(
        "source_builder_and_table",
        r#"
using System;
using System.Collections;
using System.Collections.Generic;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

[CollectionBuilder(typeof(Tokens), methodName: "Create")]
readonly struct Tokens : IEnumerable<int>
{
    private readonly int[] _items;
    private Tokens(int[] items) { _items = items; }
    public static Tokens Create(ReadOnlySpan<int> items) => new Tokens(items.ToArray());
    public int Count => _items?.Length ?? 0;
    public IEnumerator<int> GetEnumerator() => ((IEnumerable<int>)(_items ?? new int[0])).GetEnumerator();
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}

class Table
{
    internal static readonly string[,] Qualifiers = { { "", "M" }, { "S", "SM" } };
    private readonly int[,] _cells = { { 1, 2, 3 }, { 4, 5, 6 } };
    public int Cell(int row, int column) => _cells[row, column];
}

static class Program
{
    static int Classify(List<int> xs)
    {
        switch (xs)
        {
            case []: return 0;
            case [var only]: return only;
            case [1, ..]: return -1;
        }
        return xs.Count;
    }

    static void Main()
    {
        Tokens none = [];
        Tokens some = [4, 5, 6];
        Console.WriteLine(none.Count + " " + some.Count);
        Console.WriteLine(Table.Qualifiers[1, 1] + Table.Qualifiers.Length);
        Console.WriteLine(new Table().Cell(1, 2));
        Console.WriteLine(Classify(new List<int>()) + " " + Classify(new List<int> { 9 }) + " " + Classify(new List<int> { 1, 2 }) + " " + Classify(new List<int> { 2, 3, 4 }));
        var map = new Dictionary<string, int> { ["a"] = 1 };
        CollectionsMarshal.GetValueRefOrNullRef(map, "a") = 5;
        Console.WriteLine(map["a"]);
    }
}
"#,
        "0 3\nSM4\n6\n0 9 -1 3\n5\n",
    );
}

#[test]
fn a_collection_expression_is_never_one_expanded_params_element() {
    check(
        "collection_expression_and_params",
        r#"
using System;
using System.Collections.Generic;
class Stmt { }
class Local { }
static class Program
{
    static int Block(params Stmt[] statements) => statements.Length;
    static int Block(List<Local> locals, params Stmt[] statements) => locals.Count * 10 + statements.Length;
    static int Count(int[] values) => values.Length;
    static void Main(string[] args)
    {
        var local = new Local();
        Console.WriteLine(Block([local], new Stmt(), new Stmt()));
        Console.WriteLine(Block(new Stmt()));
        bool flag = args.Length == 0;
        Console.WriteLine(Count(flag ? [] : [1, 2]));
        int[] xs = flag ? [3] : [];
        Console.WriteLine(xs.Length);
        ReadOnlySpan<object> extra = new object[] { "b", "c" };
        object[] all = ["a", .. extra];
        Console.WriteLine(all.Length + (string)all[2]);
    }
}
"#,
        "12\n1\n0\n1\n3c\n",
    );
}

#[test]
fn a_bare_default_and_a_conditional_of_collections_take_the_type_they_are_put_beside() {
    check(
        "default_branch_and_collection_conditional",
        r#"
using System;

struct State
{
    public int Value;
    public string Describe(string prefix, bool annotated = false) => prefix + Value + annotated;
}

class Node
{
    public string Name;
    public Node(string name) { Name = name; }
}

static class Program
{
    static State Result => new State { Value = 4 };

    static int Call(Node receiver, params Node[] arguments) => arguments.Length;

    static void Main(string[] args)
    {
        var state = args.Length == 0 ? default : Result;
        Console.WriteLine(state.Describe("v"));
        var other = args.Length != 0 ? default : Result;
        Console.WriteLine(other.Value);
        Node right = args.Length == 0 ? null : new Node("r");
        Node temp = new Node("t");
        Console.WriteLine(Call(temp, right is null ? [] : [right]));
        Console.WriteLine(Call(temp, new Node("a"), new Node("b")));
    }
}
"#,
        "v0False\n4\n0\n2\n",
    );
}

#[test]
fn an_async_lambda_and_an_async_local_function_run_as_machines_of_their_own() {
    check(
        "async_closures",
        r#"
using System;
using System.Collections.Generic;
using System.Threading.Tasks;

class Worker
{
    public int Base = 100;

    public async Task<int> RunAsync(int seed)
    {
        int count = 0;
        Func<int, Task<int>> plain = async x =>
        {
            await Task.Delay(1);
            return x + 1;
        };
        Func<int, Task<int>> capturing = async x =>
        {
            await Task.Yield();
            count += x;
            return count + Base;
        };
        async Task<string> Describe(string prefix, int times)
        {
            var parts = new List<string>();
            for (int i = 0; i < times; i++)
            {
                await Task.Delay(1);
                parts.Add(prefix + i + count);
            }
            return string.Join(",", parts);
        }
        int a = await plain(seed);
        int b = await capturing(a);
        int c = await capturing(1);
        string d = await Describe("p", 2);
        Func<Task> inner = async () =>
        {
            await Task.Delay(1);
            count *= 2;
        };
        await inner();
        return a + b + c + count + d.Length;
    }

    public static async Task<T> Twice<T>(T value, Func<T, T> apply)
    {
        Func<Task<T>> once = async () =>
        {
            await Task.Yield();
            return apply(value);
        };
        return apply(await once());
    }
}

static class Program
{
    static void Main() => MainAsync().GetAwaiter().GetResult();

    static async Task MainAsync()
    {
        int count = 0;
        Func<int, Task<int>> add = async n =>
        {
            await Task.Delay(1);
            count += n;
            return count;
        };
        Console.WriteLine(await add(3) + await add(4));
        var worker = new Worker();
        Console.WriteLine(await worker.RunAsync(5));
        Console.WriteLine(await Worker.Twice(3, x => x * 3));
        Action<string> log = async message =>
        {
            await Task.Delay(1);
            Console.WriteLine("logged " + message);
        };
        log("m");
        await Task.Delay(50);
        Console.WriteLine(count);
    }
}
"#,
        "10\n240\n27\nlogged m\n7\n",
    );
}

#[test]
fn a_local_function_with_a_yield_is_an_iterator_of_its_own() {
    check(
        "local_function_iterators",
        r#"
using System;
using System.Collections.Generic;
using System.Threading.Tasks;
static class Program
{
    static IEnumerable<int> Evens(IEnumerable<int> source)
    {
        return filter(source);

        static IEnumerable<int> filter(IEnumerable<int> items)
        {
            foreach (var item in items)
            {
                if (item % 2 == 0) yield return item;
            }
        }
    }
    static int Count(List<int> xs)
    {
        int total = 0;
        foreach (var x in walk()) total += x;
        return total;

        IEnumerable<int> walk()
        {
            foreach (var x in xs) yield return x * 2;
        }
    }
    static async Task<int> Nested()
    {
        int seen = 0;
        await tryProcess();
        return seen;

        async Task tryProcess()
        {
            var (first, second) = Split(42);
            await Task.Delay(1);
            process(first);
            seen += second;
        }
        void process(int first) { seen += first; }
    }
    static (int a, int b) Split(int n) => (n / 10, n % 10);
    static void Main()
    {
        Console.WriteLine(string.Join(",", Evens(new[] { 1, 2, 3, 4 })));
        Console.WriteLine(Count(new List<int> { 1, 2, 3 }));
        Console.WriteLine(Nested().GetAwaiter().GetResult());
    }
}
"#,
        "2,4\n12\n6\n",
    );
}

#[test]
fn a_lambda_whose_variables_an_inner_closure_captures_gets_a_class_of_its_own() {
    check(
        "nested_display_classes",
        r#"
using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;

class Counter
{
    public int Base = 100;

    public Func<int, Func<int, int>> Adder() => a => b => a + b + Base;

    public int Sum(int[] values)
    {
        int total = 0;
        Func<int, Action> add = a =>
        {
            int twice = a * 2;
            return () => total += a + twice + Base;
        };
        foreach (var value in values) add(value)();
        return total;
    }

    public static string Tags(IEnumerable<string> names, string prefix)
    {
        Func<string, IEnumerable<string>> expand = name =>
        {
            IEnumerable<string> variants(int count)
            {
                for (int i = 0; i < count; i++) yield return prefix + name + i;
            }
            return variants(2).Where(v => v.Length > name.Length);
        };
        return string.Join(",", names.SelectMany(expand));
    }

    public static T Pick<T>(T[] items, Func<T, T, bool> better)
    {
        Func<T, Func<T, T>> best = seed => candidate => better(candidate, seed) ? candidate : seed;
        return items.Skip(1).Aggregate(items[0], (acc, item) => best(acc)(item));
    }

    public async Task<int> Later(int seed)
    {
        int count = seed;
        await Task.Delay(1);
        Func<int, Func<int, int>> make = a => b => a * b + count + Base;
        var f = make(3);
        await Task.Delay(1);
        return f(4) + make(1)(1);
    }
}

static class Program
{
    static void Main()
    {
        var counter = new Counter();
        var add = counter.Adder();
        var add1 = add(1);
        var add2 = add(2);
        Console.WriteLine(add1(10) + " " + add2(10));
        Console.WriteLine(counter.Sum(new[] { 1, 2, 3 }));
        Console.WriteLine(Counter.Tags(new[] { "x", "yy" }, "p"));
        Console.WriteLine(Counter.Pick(new[] { 3, 9, 4 }, (c, s) => c > s));
        Console.WriteLine(counter.Later(5).GetAwaiter().GetResult());
    }
}
"#,
        "111 112\n318\npx0,px1,pyy0,pyy1\n9\n223\n",
    );
}

#[test]
fn an_await_in_a_loop_condition_a_short_circuit_and_a_catch_is_rewritten() {
    check(
        "await_positions",
        r#"
using System;
using System.Collections.Generic;
using System.Threading.Tasks;
using System.Threading.Channels;
static class Program
{
    static async Task<int> Sum(ChannelReader<int> reader)
    {
        int total = 0;
        while (await reader.WaitToReadAsync())
        {
            while (reader.TryRead(out var item)) total += item;
        }
        return total;
    }
    static async Task<bool> Check(bool first, Func<Task<bool>> second)
    {
        bool both = first && await second();
        bool either = first || await second();
        int picked = first ? await Count() : 0;
        return both || either || picked > 0;
    }
    static async Task<int> Count() { await Task.Yield(); return 3; }
    static async Task<string> Guarded(bool fail)
    {
        string log = "";
        try
        {
            log += "try;";
            if (fail) throw new InvalidOperationException("boom");
            log += "ok;";
        }
        catch (InvalidOperationException e)
        {
            await Task.Delay(1);
            log += "caught " + e.Message + ";";
        }
        finally
        {
            log += "finally";
        }
        await Task.Yield();
        return log;
    }
    static async Task<int> Nested()
    {
        int seen = 0;
        await tryProcess();
        return seen;

        async Task tryProcess()
        {
            try
            {
                if (seen == 0)
                {
                    var (first, second) = split(42);
                    System.Diagnostics.Debug.Assert(first > 0);
                    process(first, second);
                }
                await Task.Delay(1);
            }
            finally
            {
                seen += 100;
            }
        }
        static (int a, int b) split(int n) => (n / 10, n % 10);
        void process(int first, int second) { seen += first + second; }
    }
    static async Task<int> Workers(int count)
    {
        var tasks = new Task<int>[count];
        for (int i = 0; i < count; i++)
        {
            int index = i;
            tasks[i] = Task.Run(async () => await Count().ConfigureAwait(false) + index);
        }
        int total = 0;
        foreach (var task in tasks) total += await task;
        return total;
    }
    static void Main()
    {
        var channel = Channel.CreateUnbounded<int>();
        channel.Writer.TryWrite(2); channel.Writer.TryWrite(5); channel.Writer.Complete();
        Console.WriteLine(Sum(channel.Reader).GetAwaiter().GetResult());
        Console.WriteLine(Check(true, () => Task.FromResult(false)).GetAwaiter().GetResult());
        Console.WriteLine(Guarded(true).GetAwaiter().GetResult());
        Console.WriteLine(Guarded(false).GetAwaiter().GetResult());
        Console.WriteLine(Nested().GetAwaiter().GetResult());
        Console.WriteLine(Workers(3).GetAwaiter().GetResult());
    }
}
"#,
        "7\nTrue\ntry;caught boom;finally\ntry;ok;finally\n106\n12\n",
    );
}

#[test]
fn a_local_function_nested_in_another_reads_its_parameters_from_the_machine() {
    check(
        "nested_local_function_parameters",
        r#"
using System;
using System.Threading.Tasks;
static class Program
{
    static async Task<int> Compute(int seed)
    {
        int result = 0;
        await Task.Delay(1);
        process(seed, 3);
        return result;

        void process(int factor, int count)
        {
            for (int i = 0; i < count; i++)
            {
                if (!tryStep(i)) break;
            }

            bool tryStep(int step)
            {
                result += step * factor;
                Func<int> peek = () => factor + step;
                return peek() < 20;
            }
        }
    }
    static void Main() => Console.WriteLine(Compute(5).GetAwaiter().GetResult());
}
"#,
        "15\n",
    );
}

#[test]
fn an_extern_method_and_an_extern_local_function_call_into_an_unmanaged_library() {
    check(
        "pinvoke",
        r#"
using System;
using System.Runtime.InteropServices;
static class Program
{
    [DllImport("libc", EntryPoint = "getpid")]
    static extern int GetPid();
    static int Twice(int x)
    {
        return Local(x) * 2;
        [DllImport("libc", EntryPoint = "abs")]
        static extern int Local(int value);
    }
    static void Main()
    {
        Console.WriteLine(GetPid() > 0);
        Console.WriteLine(Twice(-4));
    }
}
"#,
        "True\n8\n",
    );
}

#[test]
fn a_query_with_let_a_second_from_orderby_and_group_is_the_calls_it_stands_for() {
    check(
        "query_clauses",
        r#"
using System;
using System.Collections.Generic;
using System.Linq;

static class Program
{
    static int? TryParse(string text) => int.TryParse(text, out var value) ? value : (int?)null;

    static void Main()
    {
        var texts = new[] { "12", "x", "7", "30" };
        var numbers = from text in texts
                      let parsed = TryParse(text)
                      where parsed != null
                      select parsed.Value * 2;
        Console.WriteLine(string.Join(",", numbers));

        var names = new[] { "A.B.C", "D.E" };
        var parts = from full in names.Distinct()
                    from part in full.Split(new[] { '.' }, StringSplitOptions.RemoveEmptyEntries)
                    select part;
        Console.WriteLine(string.Join("", parts));

        var table = new Dictionary<string, int[]> { ["k"] = new[] { 5, 1 }, ["j"] = new[] { 3 } };
        var ordered = from entry in table
                      from value in entry.Value
                      orderby value descending, entry.Key
                      select entry.Key + value;
        Console.WriteLine(string.Join(",", ordered));

        var words = new[] { "apple", "avocado", "banana", "blueberry", "cherry" };
        var groups = from word in words
                     group word by word[0] into g
                     select g.Key + ":" + g.Count();
        Console.WriteLine(string.Join(" ", groups));

        var lengths = from word in words
                      let n = word.Length
                      let first = word[0]
                      where n > 5
                      orderby n, first descending
                      select first + n.ToString();
        Console.WriteLine(string.Join(",", lengths));
        Console.WriteLine(new List<int>(from kv in table.Values from n in kv orderby n select n).Count);
    }
}
"#,
        "24,14,60\nABCDE\nk5,j3,k1\na:2 b:2 c:1\nc6,b6,a7,b9\n3\n",
    );
}

#[test]
fn an_anonymous_object_is_a_class_with_a_property_per_member() {
    check(
        "anonymous_objects",
        r#"
using System;
using System.Collections.Generic;
using System.Linq;

static class Program
{
    static void Main()
    {
        var a = new { i = 3, d = "x" };
        Console.WriteLine(a.i + " " + a.d);
        int k = 7;
        string name = "n";
        var b = new { k, name };
        Console.WriteLine(b.k + b.name);
        var dict = new Dictionary<int, List<int>> { { 1, new List<int> { 3, 2 } }, { 5, new List<int> { 9 } } };
        var q = from i in dict from d in i.Value orderby d select new { i = i.Key, d };
        foreach (var item in q) Console.Write(item.i + ":" + item.d + " ");
        Console.WriteLine(q.First().i);
        Console.WriteLine(dict.Count + " " + dict[1].Count);
    }
}
"#,
        "3 x\n7n\n1:2 1:3 5:9 1\n2 2\n",
    );
}

#[test]
fn an_iterator_in_a_struct_walks_a_copy_of_the_struct() {
    check(
        "struct_iterator",
        r#"
using System;
using System.Collections.Generic;

struct Bits
{
    private ulong _bits0;
    private ulong[] _bits;
    private int _capacity;

    public static Bits Create(int capacity) => new Bits { _bits = new ulong[2], _capacity = capacity };

    public bool this[int index]
    {
        set
        {
            if (index < 64) _bits0 |= 1UL << index;
            else _bits[(index >> 6) - 1] |= 1UL << (index & 63);
        }
    }

    public IEnumerable<int> TrueBits()
    {
        for (int bit = 0; bit < 64; bit++)
        {
            if ((_bits0 & (1UL << bit)) != 0) yield return bit;
        }
        for (int i = 0; i < _bits.Length; i++)
        {
            for (int b = 0; b < 64; b++)
            {
                if ((_bits[i] & (1UL << b)) != 0)
                {
                    int bit = ((i + 1) << 6) | b;
                    if (bit >= _capacity) yield break;
                    yield return bit;
                }
            }
        }
    }
}

static class Program
{
    static void Main()
    {
        var bits = Bits.Create(100);
        bits[3] = true;
        bits[70] = true;
        bits[99] = true;
        Console.WriteLine(string.Join(" ", bits.TrueBits()));
    }
}
"#,
        "3 70 99\n",
    );
}

#[test]
fn a_nullable_bool_joins_a_string_without_lifting_and_an_untyped_hole_is_an_object() {
    check(
        "nullable_concat",
        r#"
using System;

class Sym
{
    public bool HasRef = true;
    public bool IsNullable = false;
    public object Type;

    public bool? Calc() => HasRef ? !IsNullable : (bool?)null;
    public int? Neg(int a) => -a;
    public long? Widen(int a) { return a; }
    public string Show() => $"{GetType().Name} Type: {(Type is null ? "null" : Type)}";
}

static class Program
{
    static void Main()
    {
        var s = new Sym();
        Console.WriteLine(s.Calc() + " " + (s.Calc() == null) + " " + s.Neg(4) + " " + s.Widen(9));
        Console.WriteLine(s.Show());
        s.Type = 5;
        Console.WriteLine(s.Show());
        int n = 2;
        Console.WriteLine($"{(n switch { 1 => "one", _ => n })}");
    }
}
"#,
        "True False -4 9\nSym Type: null\nSym Type: 5\n2\n",
    );
}

#[test]
fn an_embedded_string_resource_is_read_back_by_a_resource_manager() {
    let resource = rustlyn_emit::Resource::strings(
        "Demo.Strings.resources",
        &[
            ("Greeting".to_string(), "hello, {0}".to_string()),
            (
                "ERR_BadThing".to_string(),
                "bad thing: '{0}' \u{00e9}".to_string(),
            ),
            ("Empty".to_string(), String::new()),
        ],
    );
    check_with_resources(
        "resources",
        r#"
using System;
using System.Resources;

static class Program
{
    static void Main()
    {
        var names = typeof(Program).Assembly.GetManifestResourceNames();
        Console.WriteLine(string.Join(",", names));
        var manager = new ResourceManager("Demo.Strings", typeof(Program).Assembly);
        Console.WriteLine(string.Format(manager.GetString("Greeting"), "world"));
        Console.WriteLine(manager.GetString("ERR_BadThing"));
        Console.WriteLine("[" + manager.GetString("Empty") + "]");
        Console.WriteLine(manager.GetString("Missing") == null);
    }
}
"#,
        std::slice::from_ref(&resource),
        "Demo.Strings.resources\nhello, world\nbad thing: '{0}' \u{00e9}\n[]\nTrue\n",
    );
}

#[test]
fn a_private_overload_of_another_class_is_not_a_candidate() {
    check(
        "private_overload",
        r#"
using System;

class Test
{
    public int Id;
    public override bool Equals(object obj) => Equals(obj as Test);
    private bool Equals(Test other) => other != null && other.Id == Id;
    public override int GetHashCode() => Id;

    class Nested
    {
        public static bool Same(Test a, Test b) => a.Equals(b);
    }

    public static bool ViaNested(Test a, Test b) => Nested.Same(a, b);
}

static class Program
{
    static void Main()
    {
        var a = new Test { Id = 1 };
        var b = new Test { Id = 1 };
        Test none = null;
        Console.WriteLine(a.Equals(b) + " " + a.Equals(none) + " " + Test.ViaNested(a, b) + " " + a.Equals((object)b));
    }
}
"#,
        "True False True True\n",
    );
}

#[test]
fn a_this_ref_extension_gets_its_receiver_by_reference() {
    check(
        "this_ref_extension",
        r#"
using System;

struct Counter
{
    public int Count;
}

static class CounterExtensions
{
    public static void AddIfNotNull<T>(this ref Counter counter, T value) where T : class
    {
        if (value != null) counter.Count++;
    }

    public static void Bump(this ref Counter counter) => counter.Count += 10;
}

static class Program
{
    static void Fill(ref Counter counter, string a, string b)
    {
        counter.AddIfNotNull(a);
        counter.AddIfNotNull(b);
    }

    static void Main()
    {
        var counter = new Counter();
        Fill(ref counter, "x", null);
        counter.Bump();
        Console.WriteLine(counter.Count);
    }
}
"#,
        "11\n",
    );
}

#[test]
fn a_static_lambda_in_a_struct_stays_static_whatever_a_default_argument_names() {
    check(
        "struct_static_lambda",
        r#"
using System;
using System.Collections.Generic;

enum Annotation { Oblivious, NotAnnotated, Annotated }

readonly struct Typed
{
    public readonly string Name;
    public Annotation Annotation { get; }
    private Typed(string name, Annotation annotation) { Name = name; Annotation = annotation; }
    public static Typed Create(string name, Annotation annotation = Annotation.Oblivious) => new Typed(name, annotation);
    public Func<string, Typed> Maker() => static name => Typed.Create(name);
    public Func<string, Typed> Maker2() => name => Create(name, Annotation.Annotated);
}

static class Ext
{
    public static List<R> SelectAsArray<T, R, A>(this List<T> items, Func<T, int, A, R> map, A arg)
    {
        var result = new List<R>();
        for (int i = 0; i < items.Count; i++) result.Add(map(items[i], i, arg));
        return result;
    }
}

struct Inferrer
{
    private readonly List<string> _names;
    private readonly (Typed Type, bool Fixed)[] _results;
    public Inferrer(List<string> names, (Typed, bool)[] results) { _names = names; _results = results; }
    private bool IsUnfixed(int i) => !_results[i].Fixed;
    public List<Typed> Fixed() => _names.SelectAsArray(
        static (name, i, self) => self.IsUnfixed(i) ? Typed.Create(name) : self._results[i].Type,
        this);
}

static class Program
{
    static void Main()
    {
        var t = Typed.Create("x", Annotation.Annotated);
        Console.WriteLine(t.Maker()("a").Annotation + " " + t.Maker2()("b").Annotation);
        var inferrer = new Inferrer(
            new List<string> { "a", "b", "c" },
            new[] { (Typed.Create("x"), false), (Typed.Create("y"), true), (Typed.Create("z"), false) });
        foreach (var made in inferrer.Fixed()) Console.Write(made.Name + ":" + made.Annotation + " ");
        Console.WriteLine();
    }
}
"#,
        "Oblivious Annotated\na:Oblivious y:Oblivious c:Oblivious \n",
    );
}

#[test]
fn a_conversion_operator_taking_in_gets_the_operands_address() {
    check(
        "in_operator",
        r#"
using System;

struct Builder
{
    public int Count;
    public static implicit operator Plain(in Builder b) => new Plain { Count = b.Count };
    public static explicit operator int(in Builder b) => b.Count * 10;
}

struct Plain { public int Count; }

static class Program
{
    static void Take(Plain p) => Console.Write(p.Count + " ");

    static void Main()
    {
        var b = new Builder { Count = 4 };
        Take(b);
        Plain p = b;
        int n = (int)b;
        Console.WriteLine(p.Count + " " + n);
    }
}
"#,
        "4 4 40\n",
    );
}

#[test]
fn a_field_address_through_a_type_parameter_is_taken_off_the_reference() {
    check(
        "type_parameter_field_address",
        r#"
using System;

struct Bits
{
    public int[] Words;
    public int Cap;
    public void Ensure(int n) { if (n > Cap) { Array.Resize(ref Words, n); Cap = n; } }
}

abstract class Usages<TState> { public TState FromTop; public TState FromBottom; }

class Pass<TState, TUsages> where TState : struct where TUsages : Usages<TState>
{
    public virtual bool Join(ref TState a, ref TState b) => true;
    public bool Record(TUsages current, ref TState at)
    {
        current.FromBottom = at;
        return Join(ref current.FromTop, ref at);
    }
}

class BitUsages : Usages<Bits> { }

class BitPass : Pass<Bits, BitUsages>
{
    public override bool Join(ref Bits a, ref Bits b) { a.Ensure(3); b.Ensure(5); return a.Cap == 3; }
}

static class Program
{
    static void Main()
    {
        var pass = new BitPass();
        var usages = new BitUsages { FromTop = new Bits { Words = new int[1], Cap = 1 } };
        var at = new Bits { Words = new int[1], Cap = 1 };
        var ok = pass.Record(usages, ref at);
        Console.WriteLine(ok + " " + usages.FromTop.Cap + " " + usages.FromBottom.Cap + " " + at.Cap);
    }
}
"#,
        "True 3 1 5\n",
    );
}

#[test]
fn a_generic_record_names_its_members_through_its_own_construction() {
    check(
        "generic_records",
        r#"
using System;

readonly record struct Entry<T>(T Item, int State);
record Box<T>(T Value, string Tag);

static class Program
{
    static void Main()
    {
        var a = new Entry<string>("x", 1);
        var b = new Entry<string>("x", 1);
        var c = new Box<int>(3, "t");
        var d = c with { Tag = "u" };
        Console.WriteLine(a.Equals(b) + " " + (a == b) + " " + (a != b) + " " + (a.GetHashCode() == b.GetHashCode()) + " " + a + " " + (c == d) + " " + (c == new Box<int>(3, "t")) + " " + d);
    }
}
"#,
        "True True False True Entry { Item = x, State = 1 } False True Box { Value = 3, Tag = u }\n",
    );
}

#[test]
fn a_type_parameter_is_boxed_before_a_null_test_and_a_constant_loop_tests_nothing() {
    check(
        "boxed_null_test",
        r#"
using System;

class Pool<T> where T : class
{
    T _first;
    public bool Free(T obj) { if (_first == null) { _first = obj; return true; } return obj != null && _first == obj; }
}

static class Program
{
    static int Combine<T>(T key, int hash) => key == null ? hash : key.GetHashCode() + hash;
    static string Loop(int n) { while (true) { if (n > 3) return "big"; n++; } }
    static string Root(string path)
    {
        if (path.Length > 2) { if (path[0] == 'a') return "a"; return path; }
        else if (path.Length == 2) { return path.Length > 1 ? "x" : "y"; }
        else { return ""; }
    }

    static void Main()
    {
        var p = new Pool<string>();
        Console.WriteLine(p.Free("a") + " " + p.Free("a") + " " + Combine<string>(null, 1) + " " + Combine(5, 1) + " " + Loop(0) + " " + Root("abc") + Root("ab") + Root(""));
    }
}
"#,
        "True True 1 6 big ax\n",
    );
}

#[test]
fn a_long_constant_an_enum_cast_and_a_ref_conditional_come_out_at_their_own_types() {
    check(
        "long_constant_ref_conditional",
        r#"
using System;

enum Kind { A, B, C }

struct Packed
{
    const int Offset = 0;
    const long Mask = 0x1F;
    long _bits;
    public Kind Kind { get => (Kind)((_bits >> Offset) & Mask); set => _bits = (_bits & ~(Mask << Offset)) | ((long)value << Offset); }
    public static ulong AllSet(int n) => n == 64 ? ~0UL : (1UL << n) - 1;
}

class Doc
{
    string _a, _b;
    static string Get(ref string slot) { slot ??= "made"; return slot; }
    public string Xml(bool expanded) { ref var lazy = ref expanded ? ref _a : ref _b; return Get(ref lazy); }
    public ref string Slot(bool expanded) => ref expanded ? ref _a : ref _b;
}

static class Program
{
    static void Main()
    {
        var p = new Packed();
        p.Kind = Kind.C;
        var d = new Doc();
        d.Slot(false) = "b";
        Console.WriteLine(p.Kind + " " + Packed.AllSet(3) + " " + d.Xml(true) + d.Xml(false) + " " + d.Slot(true));
    }
}
"#,
        "C 7 madeb made\n",
    );
}

#[test]
fn a_collection_expression_picks_an_overload_its_elements_fit_and_a_list_pattern_reads_a_span() {
    check(
        "collection_overloads",
        r#"
using System;
using System.Collections.Generic;

enum V { One = 1, Two = 2 }

static class Program
{
    static string Take(params string[] items) => "s" + items.Length;
    static string Take(params object[] items) => "o" + items.Length;
    static int Sum(IEnumerable<int> xs) { int s = 0; foreach (var x in xs) s += x; return s; }
    static string P(int code, params object[] args) => code + ":" + string.Join(",", args);

    static short? Scan(ReadOnlySpan<char> s)
    {
        if (s is { Length: >= 1 and <= 5 } and not ['0', ..])
        {
            int v = 0;
            foreach (char d in s) { if (d < '0' || d > '9') return null; v = v * 10 + (d - '0'); }
            return (short)v;
        }
        return null;
    }

    static string Fill(ulong size)
    {
        object[] labels = new object[size];
        long total = 0;
        for (ulong i = 0; i < size; ++i) { labels[i] = i * 2; total += (long)i; }
        long k = 1;
        labels[k] = "one";
        labels[k] += "!";
        return labels.Length + " " + labels[3] + " " + labels[1] + " " + total;
    }

    static void Main()
    {
        Console.WriteLine(string.Join(", ", [(int)V.One, (int)V.Two]) + " " + Take(["a", "b"]) + " " + Take(["a", 1]) + " " + Sum([1, 2, 3]) + " " + string.Join("|", ["x", null]));
        Console.WriteLine(P(1, "level", 4) + " " + P(2) + " " + Scan("123") + " " + (Scan("0123") == null) + " " + Scan("12x") + " " + Fill(4));
    }
}
"#,
        "1, 2 s2 o2 6 x|\n1:level,4 2: 123 True  4 6 one! 6\n",
    );
}

#[test]
fn a_struct_reaches_value_type_through_base_and_readonly_fields_are_called_on_copies() {
    check(
        "struct_base_and_readonly",
        r#"
using System;

struct Refd : IEquatable<Refd>
{
    public int A;
    public override bool Equals(object obj) => obj is Refd && base.Equals((Refd)obj);
    public bool Equals(Refd other) => A == other.A;
    public override int GetHashCode() => A;
}

struct Pt { public int X; public int Bump() { X++; return X; } public readonly int Peek() => X; }

class Node { }
class Leaf : Node { }

class Holder
{
    static readonly char[] s_delims = { ':', '.', '+' };
    static readonly Pt s_origin = new Pt { X = 5 };
    readonly Pt _pt = new Pt { X = 7 };
    readonly Func<int> _f;
    public Holder(int seed) : this(seed, "x") { }
    public Holder(int seed, string tag) { var local = seed * 2; _f = () => local + tag.Length; }
    public string Run() => new string(s_delims) + " " + s_origin.Bump() + s_origin.X + " " + _pt.Bump() + _pt.X + " " + _pt.Peek() + " " + _f();
}

static class Program
{
    static T As<T>(object o) where T : class => o as T;
    static bool Present<T>(T x) where T : class => x is object;

    static void Main()
    {
        var a = new Refd { A = 1 };
        Console.WriteLine(a.Equals((object)new Refd { A = 1 }) + " " + a.Equals((object)new Refd { A = 2 }) + " " + (As<Leaf>(new Leaf()) != null) + " " + (As<Leaf>(new Node()) == null) + " " + Present("x") + " " + Present<string>(null));
        var bytes = new byte[] { 1, 2 };
        var longs = new long[] { 3L };
        bytes[1] += 5;
        Console.WriteLine(new Holder(4).Run() + " " + bytes[1] + longs[0]);
    }
}
"#,
        "True False True True True False\n:.+ 65 87 7 9 73\n",
    );
}

#[test]
fn a_nullable_coalesced_with_a_nullable_stays_one_and_primitives_load_with_their_own_ldelem() {
    check(
        "nullable_coalesce",
        r#"
using System;

class Sym
{
    public byte? Local;
    public Sym Parent;
    public byte? Context() => Local ?? Parent?.Context();
    public int Pick(byte? a, byte? b) => a ?? b ?? 9;
}

static class Program
{
    static void Main()
    {
        var root = new Sym { Local = 3 };
        var child = new Sym { Parent = root };
        var chars = "héllo".ToCharArray();
        var shorts = new short[] { -2 };
        var bools = new[] { true };
        var bytes = new byte[] { 200 };
        var strs = new[] { "s" };
        int sum = 0;
        foreach (var c in chars) sum += c;
        Console.WriteLine(child.Context() + " " + new Sym().Context().HasValue + " " + root.Pick(null, 4) + root.Pick(null, null) + " " + chars[1] + shorts[0] + bools[0] + bytes[0] + strs[0] + " " + sum);
    }
}
"#,
        "3 False 49 \u{e9}-2True200s 664\n",
    );
}

#[test]
fn a_lambda_calling_a_capturing_local_function_lives_with_its_captures() {
    check(
        "lambda_calls_local_function",
        r#"
using System;
using System.Collections.Generic;

class Conv
{
    int _n = 100;
    readonly Dictionary<int, int> _frames = new();

    public string Run(List<int> xs, int seed)
    {
        xs.ForEach(x => { if (x > 0) { var f = Make(x); _frames[x] = f; } });
        int Make(int v) => v + xs.Count + seed + _n;
        return string.Join(",", _frames.Values);
    }

    static (int, int)? Pair(bool b) { if (b) return (1, 2); return null; }
    static (int a, int b)? Pair2(bool b) => b ? (3, 4) : null;

    static void Main()
    {
        Console.WriteLine(new Conv().Run(new List<int> { -1, 2, 3 }, 10) + " " + Pair(true) + " " + Pair(false).HasValue + " " + Pair2(true)?.a);
    }
}
"#,
        "115,116 (1, 2) False 3\n",
    );
}

#[test]
fn a_protected_base_property_is_set_through_this_and_a_rectangular_array_is_walked() {
    check(
        "protected_base_and_rectangular_array",
        r#"
using System;
using System.Collections.Generic;

class Node { protected int Level { get; set; } public int Read() => Level; }

class Expr : Node
{
    public new int Level { get => base.Level; set => base.Level = value; }
    public void Bump() { base.Level += 2; this.Level++; }
}

static class Program
{
    static readonly string[,] s_grid = { { "", "M" }, { "S", "SM" } };

    static void Main()
    {
        var e = new Expr { Level = 5 };
        e.Bump();
        var parts = new List<string>();
        foreach (var q in s_grid) parts.Add("<" + q + ">");
        foreach (string q in s_grid) parts.Add(q.Length.ToString());
        Console.WriteLine(e.Read() + " " + string.Concat(parts) + " " + s_grid.Length + s_grid[1, 1]);
    }
}
"#,
        "8 <><M><S><SM>0112 4SM\n",
    );
}

#[test]
fn a_coalesce_converts_its_left_through_an_operator_and_a_tuple_widens_element_by_element() {
    check(
        "coalesce_operator_and_tuple_widening",
        r#"
using System;
using System.Collections;
using System.Collections.Generic;
using System.Collections.Immutable;

class Base { public virtual string N => "b"; }
class Derived : Base { public override string N => "d"; }

struct Bag : IEnumerable<Derived>
{
    public IEnumerator<Derived> GetEnumerator() { yield return new Derived(); }
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}

readonly struct NodeOrToken
{
    public readonly string Text;
    public NodeOrToken(string t) { Text = t; }
    public static implicit operator NodeOrToken(Base b) => new NodeOrToken(b == null ? "null" : b.N);
}

static class Program
{
    static int Count(IEnumerable<Base> items) { int n = 0; foreach (var i in items) n++; return n; }
    static bool Nameof(bool? cached, bool actual) { bool r = cached ??= actual; return r && cached.Value; }
    static (IEnumerable<int>, IEnumerable<string>) Widen((ImmutableArray<int>, ImmutableArray<string>) t) => t;

    static void Main()
    {
        Base b = new Derived();
        Base none = null;
        NodeOrToken tok = b ?? (NodeOrToken)new Base();
        NodeOrToken tok2 = none ?? new NodeOrToken("t");
        var pair = (ImmutableArray.Create(1, 2), ImmutableArray.Create("x"));
        var wide = Widen(pair);
        int wn = 0;
        foreach (var x in wide.Item1) wn++;
        Console.WriteLine(Count(new Bag()) + " " + tok.Text + tok2.Text + " " + Nameof(null, true) + Nameof(false, true) + " " + wn);
    }
}
"#,
        "1 dt TrueFalse 2\n",
    );
}

#[test]
fn inference_takes_a_tuple_upper_bound_and_finds_a_return_inside_try() {
    check(
        "inference_tuple_bound_and_try_return",
        r#"
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading;

class Node { public int V = 1; }
class Str : Node { public override string ToString() => "str"; }

readonly struct Provider<T> { public readonly T[] Items; public Provider(T[] items) { Items = items; } }

static class Ext
{
    public static TResult Rewrite<TI, TArg, TResult>(this Node n, TArg arg, Func<TI, int, TArg, TResult> f1, Func<Node, TResult, TResult, TArg, TResult> f2) where TI : Node
        => f2(n, f1(default, 1, arg), f1(default, 2, arg), arg);

    public static Provider<TResult> SelectMany<TSource, TResult>(this Provider<TSource> source, Func<TSource, CancellationToken, ImmutableArray<TResult>> selector)
    {
        var all = ImmutableArray.CreateBuilder<TResult>();
        foreach (var s in source.Items) all.AddRange(selector(s, default));
        return new Provider<TResult>(all.ToArray());
    }

    public static Provider<TResult> SelectMany<TSource, TResult>(this Provider<TSource> source, Func<TSource, CancellationToken, IEnumerable<TResult>> selector)
    {
        var all = new List<TResult>();
        foreach (var s in source.Items) all.AddRange(selector(s, default));
        return new Provider<TResult>(all.ToArray());
    }
}

class Builder<T>
{
    readonly List<T> _l = new();
    public static Builder<T> GetInstance() => new();
    public void Add(T t) => _l.Add(t);
    public ImmutableArray<T> ToImmutableAndFree() => _l.ToImmutableArray();
    public void Free() { }
}

static class Program
{
    static Provider<T> Run<T>(Provider<((string tree, ImmutableArray<int> nodes), int compilation)> p, Func<int, T> transform)
    {
        return p.SelectMany((tuple, cancellationToken) =>
        {
            var ((tree, nodes), compilation) = tuple;
            var result = Builder<T>.GetInstance();
            try
            {
                foreach (var n in nodes)
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    var sym = n > 1 ? tree : n == 1 ? "one" : null;
                    if (sym is null) continue;
                    result.Add(transform(n + compilation));
                }
                return result.ToImmutableAndFree();
            }
            finally { result.Free(); }
        });
    }

    static void Main()
    {
        Func<Str, int, (ImmutableArray<int>, Node), string> f1 = (s, i, arg) => arg.Item2 + "" + i;
        Func<Node, string, string, (ImmutableArray<int>, Node), string> f2 = (n, a, b, arg) => a + b + n.V;
        var appendCalls = ImmutableArray<int>.Empty;
        var str = new Str();
        var r = (string)new Node().Rewrite((appendCalls, str), f1, f2);
        var p = new Provider<((string, ImmutableArray<int>), int)>(new[] { (("t", ImmutableArray.Create(0, 1, 2)), 10) });
        Console.WriteLine(r + " " + string.Join(",", Run(p, x => "v" + x).Items));
    }
}
"#,
        "str1str21 v11,v12\n",
    );
}

#[test]
fn a_local_function_in_a_generic_methods_display_class_is_called_by_the_classs_own_parameter() {
    check(
        "generic_display_local_function",
        r#"
using System;
using System.Collections.Generic;
using System.Collections.Immutable;

static class Program
{
    static IEnumerable<T> Provide<T>(int[] items, Func<int, T> transform, string name)
    {
        var results = new List<T>();
        foreach (var item in items)
        {
            if (getMatching(item, name).Length > 0) results.Add(transform(item));
        }
        return results;

        static ImmutableArray<string> getMatching(int item, string name)
        {
            var result = ImmutableArray.CreateBuilder<string>();
            addMatching(item % 2 == 0 ? ImmutableArray.Create(name) : null);
            addMatching(ImmutableArray.Create("x"));
            return result.ToImmutable();

            void addMatching(ImmutableArray<string>? attributes)
            {
                if (attributes is { } list) foreach (var a in list) if (a.Length > 0) result.Add(a);
            }
        }
    }

    static void Main() => Console.WriteLine(string.Join(",", Provide(new[] { 1, 2, 3 }, i => "v" + i, "n")));
}
"#,
        "v1,v2,v3\n",
    );
}

#[test]
fn a_bare_default_takes_its_operands_type_and_a_tuples_members_go_through_value_tuple() {
    check(
        "default_beside_struct_and_tuple_members",
        r#"
using System;

[Flags] enum Wide : long { None = 0, Perf = 1L << 40 }

readonly struct Token : IEquatable<Token>
{
    public readonly int Kind;
    public Token(int k) { Kind = k; }
    public static bool operator ==(Token a, Token b) => a.Kind == b.Kind;
    public static bool operator !=(Token a, Token b) => a.Kind != b.Kind;
    public bool Equals(Token o) => Kind == o.Kind;
    public override bool Equals(object o) => o is Token t && t == this;
    public override int GetHashCode() => Kind;
}

class Src
{
    public (int? blockBody, string arrowBody) Bodies = (null, null);
    public (int? blockBody, string arrowBody) Full = (1, "a");
}

static class Program
{
    static bool HasAwait(Token t) => t != default;
    static bool NoBody(object m) => m is Src { Bodies: { arrowBody: null, blockBody: null } } and not string;

    static void Main()
    {
        Wide w = Wide.Perf;
        long raw = (long)w;
        Console.WriteLine(HasAwait(new Token(3)) + " " + HasAwait(default) + " " + NoBody(new Src()) + " " + (new Src() is { Full: { blockBody: 1 } }) + " " + raw + " " + (Wide)(1L << 40));
    }
}
"#,
        "True False True True 1099511627776 Perf\n",
    );
}

#[test]
fn the_two_parts_of_a_partial_method_are_one_method() {
    check(
        "partial_methods",
        r#"
using System;

partial class C
{
    private partial int M(int x);
    private static partial string Name();
    partial void Hook(ref int n);
    public int Run() { int n = 1; Hook(ref n); return M(n) + Name().Length; }
}

partial class C
{
    private partial int M(int value) => value * 10;
    private static partial string Name() => "abc";
    partial void Hook(ref int n) { n += 2; }
}

partial class D { partial void Never(); public int Go() { Never(); return 7; } }

static class Program { static void Main() => Console.WriteLine(new C().Run() + " " + new D().Go()); }
"#,
        "33 7\n",
    );
}

#[test]
fn a_pattern_variable_in_a_target_typed_conditional_is_declared_once() {
    check(
        "conditional_pattern_rebound",
        r#"
using System;
using System.Collections.Generic;

abstract class Node { }
class Leaf : Node { public int V; }
class Twig : Node { public string S = "t"; }

static class Program
{
    static Node Make(int v) => new Leaf { V = v };
    static Node Other(string s) => new Twig { S = s };
    static bool Try(object o, out string text) { text = o as string ?? ""; return o is string; }
    static Node Pick(object o) => Try(o, out var text) ? Other(text) : Make(1);

    static void Main()
    {
        object[] items = { new Leaf { V = 3 }, "x", new Leaf { V = 5 } };
        var list = new List<Node>();
        foreach (var item in items)
            list.Add(item is Leaf leaf ? Make(leaf.V * 2) : Other("o"));
        foreach (var n in list)
            Console.WriteLine(n is Leaf l ? l.V.ToString() : ((Twig)n).S);
        Console.WriteLine(Pick("abc") is Twig t ? t.S : "leaf");
        Console.WriteLine(Pick(7) is Twig ? "twig" : "leaf");
    }
}
"#,
        "6\no\n10\nabc\nleaf\n",
    );
}

#[test]
fn async_iterators_yield_await_and_leave_through_their_finally() {
    check(
        "async_iterator",
        r#"
using System;
using System.Collections.Generic;
using System.Runtime.CompilerServices;
using System.Threading;
using System.Threading.Tasks;

static class Program
{
    static async IAsyncEnumerable<int> Count(int limit, [EnumeratorCancellation] CancellationToken token = default)
    {
        try
        {
            for (int i = 1; i <= limit; i++)
            {
                await Task.Yield();
                token.ThrowIfCancellationRequested();
                yield return i;
            }
        }
        finally
        {
            Console.WriteLine("finally " + limit);
        }
    }

    static async IAsyncEnumerator<string> Words()
    {
        yield return "one";
        await Task.Delay(1);
        yield return "two";
    }

    static async Task Main()
    {
        int sum = 0;
        await foreach (var i in Count(4))
            sum += i;
        Console.WriteLine(sum);
        await foreach (var i in Count(10))
        {
            if (i == 2)
                break;
        }
        var numbers = Count(3);
        await using (var e = numbers.GetAsyncEnumerator())
        {
            while (await e.MoveNextAsync())
                Console.WriteLine(e.Current);
        }
        using var source = new CancellationTokenSource();
        try
        {
            await foreach (var i in Count(5).WithCancellation(source.Token))
            {
                if (i == 2)
                    source.Cancel();
            }
        }
        catch (OperationCanceledException)
        {
            Console.WriteLine("cancelled");
        }
        var words = Words();
        while (await words.MoveNextAsync())
            Console.WriteLine(words.Current);
        await words.DisposeAsync();
    }
}
"#,
        "finally 4\n10\nfinally 10\n1\n2\n3\nfinally 3\nfinally 5\ncancelled\none\ntwo\n",
    );
}

#[test]
fn await_foreach_awaits_each_step_and_disposes_however_the_loop_is_left() {
    check(
        "await_foreach",
        r#"
using System;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;

class Counter : IAsyncEnumerable<int>, IAsyncEnumerator<int>
{
    int n; readonly int limit;
    public Counter(int limit) { this.limit = limit; }
    public IAsyncEnumerator<int> GetAsyncEnumerator(CancellationToken ct = default) => this;
    public int Current => n;
    public async ValueTask<bool> MoveNextAsync() { await Task.Yield(); return ++n <= limit; }
    public ValueTask DisposeAsync() { Console.WriteLine("disposed " + limit); return default; }
}

static class Program
{
    static async Task<int> Sum(int limit)
    {
        int sum = 0;
        await foreach (var i in new Counter(limit))
        {
            if (i == 2) continue;
            sum += i;
        }
        return sum;
    }

    static async Task<int> FirstOver(int bound)
    {
        await foreach (int i in ((IAsyncEnumerable<int>)new Counter(10)).ConfigureAwait(false))
        {
            if (i > bound) return i;
        }
        return -1;
    }

    static async Task<string> Collect()
    {
        var parts = new List<string>();
        await foreach (var i in new Counter(6))
        {
            if (i == 4) break;
            parts.Add(i.ToString());
        }
        return string.Join(",", parts);
    }

    static async Task<int> Failing()
    {
        try
        {
            await foreach (var i in new Counter(3))
            {
                if (i == 2) throw new InvalidOperationException("two");
            }
        }
        catch (InvalidOperationException e)
        {
            Console.WriteLine("caught " + e.Message);
            return 99;
        }
        return 0;
    }

    static void Main()
    {
        Console.WriteLine(Sum(4).GetAwaiter().GetResult());
        Console.WriteLine(FirstOver(7).GetAwaiter().GetResult());
        Console.WriteLine(Collect().GetAwaiter().GetResult());
        Console.WriteLine(Failing().GetAwaiter().GetResult());
    }
}
"#,
        "disposed 4\n8\ndisposed 10\n8\ndisposed 6\n1,2,3\ndisposed 3\ncaught two\n99\n",
    );
}

#[test]
fn field_backed_accessors_destructors_extension_properties_and_exhaustive_switches() {
    check(
        "field_destructor_extension_switch",
        r#"
using System;
using System.Text.RegularExpressions;

class Holder
{
    public bool? Flag { get; set { if (field is not null) throw new InvalidOperationException("twice"); field = value; } }
    public int Count { get => field * 2; set; }
}

class Noisy
{
    public static int Finalized;
    ~Noisy() { Finalized++; }
}

static class Options
{
    extension(string text)
    {
        public int Doubled => text.Length * 2;
        public string Shout() { return text.ToUpperInvariant() + "!"; }
    }
}

static class Program
{
    static string Pick(bool a, bool b)
    {
        switch (a, b)
        {
            case (false, false): return "neither";
            case (false, true): return "second";
            case (true, false): return "first";
            case (true, true): return "both";
        }
    }

    static void MakeGarbage() { for (int i = 0; i < 10; i++) new Noisy(); }

    static void Main()
    {
        var h = new Holder();
        h.Flag = true;
        Console.WriteLine(h.Flag);
        try { h.Flag = false; } catch (InvalidOperationException e) { Console.WriteLine(e.Message); }
        h.Count = 21;
        Console.WriteLine(h.Count);
        Console.WriteLine("abc".Doubled + " " + "abc".Shout());
        Console.WriteLine(Pick(true, false) + " " + Pick(true, true));
        MakeGarbage();
        GC.Collect();
        GC.WaitForPendingFinalizers();
        Console.WriteLine(Noisy.Finalized > 0);
    }
}
"#,
        "True\ntwice\n42\n6 ABC!\nfirst both\nTrue\n",
    );
}

#[test]
fn an_enum_member_names_another_as_a_number_in_its_initializer() {
    check(
        "enum_member_initializers",
        r#"
using System;
[Flags]
enum K
{
    None = 0x00,
    ReferenceType = 0x01,
    ValueType = 0x02,
    Constructor = 0x04,
    Unmanaged = 0x08,
    NullableReferenceType = ReferenceType | 0x10,
    NotNullableReferenceType = ReferenceType | 0x20,
    Oblivious = 0x40,
    NotNull = 0x80,
    Default = 0x100,
    AllReferenceTypeKinds = NullableReferenceType | NotNullableReferenceType,
    AllValueTypeKinds = ValueType | Unmanaged,
    AllNonNullableKinds = NotNullableReferenceType | ValueType | Unmanaged,
}
static class P
{
    static void Main()
    {
        foreach (K k in Enum.GetValues(typeof(K))) Console.WriteLine(k + " = " + (int)k);
        K c = K.NotNullableReferenceType;
        Console.WriteLine((c & K.Unmanaged) != 0);
        Console.WriteLine((c & (K.ValueType | K.ReferenceType)) != 0);
        Console.WriteLine((c & K.AllValueTypeKinds) != 0);
    }
}
"#,
        "None = 0\nReferenceType = 1\nValueType = 2\nConstructor = 4\nUnmanaged = 8\nAllValueTypeKinds = 10\nNullableReferenceType = 17\nNotNullableReferenceType = 33\nAllNonNullableKinds = 43\nAllReferenceTypeKinds = 49\nOblivious = 64\nNotNull = 128\nDefault = 256\nFalse\nTrue\nFalse\n",
    );
}

#[test]
fn a_generic_operator_is_called_through_the_construction_that_fits_it() {
    check(
        "generic_operator_construction",
        r#"
using System;
using System.Collections.Generic;

readonly struct Pair<T> where T : class
{
    public readonly T Node;
    public Pair(T node) { Node = node; }
    public static implicit operator Pair<object>(Pair<T> pair) => new Pair<object>(pair.Node);
    public static explicit operator Pair<T>(Pair<object> pair) => new Pair<T>((T)pair.Node);
    public Wrapped<U> Wrap<U>() where U : class => new Wrapped<U>(this);
}
readonly struct Wrapped<U> where U : class
{
    public readonly Pair<object> Inner;
    public Wrapped(Pair<object> inner) { Inner = inner; }
}
struct Money : IEquatable<Money>
{
    public int Cents;
    public bool Equals(Money other) => Cents == other.Cents;
    public override bool Equals(object? obj) => (obj as Money?)?.Equals(this) ?? false;
    public override int GetHashCode() => Cents;
}
static class Program
{
    static string Show<T>(T value) => value?.ToString() ?? "null";
    static void Main()
    {
        var w = new Pair<string>("s").Wrap<Exception>();
        Console.WriteLine(w.Inner.Node);
        var back = (Pair<string>)w.Inner;
        Console.WriteLine(back.Node.Length);
        Console.WriteLine(new Money { Cents = 5 }.Equals((object)new Money { Cents = 5 }));
        Console.WriteLine(new Money { Cents = 5 }.Equals((object)"x"));
        Console.WriteLine(new Money { Cents = 5 }.Equals(null));
        Console.WriteLine(Show(7) + " " + Show<string>(null) + " " + Show("q") + " " + Show<int?>(null));
    }
}
"#,
        "s\n1\nTrue\nFalse\nFalse\n7 null q null\n",
    );
}

#[test]
fn a_switch_expression_with_a_null_arm_beside_a_value_type_is_nullable() {
    check(
        "switch_null_arm_nullable",
        r#"
using System;
enum Level { CallingMethod, ReturnOnly }
readonly struct Ctx
{
    private readonly uint _value;
    private Ctx(uint value) => _value = value;
    public static readonly Ctx CallingMethod = new Ctx(0);
    public static readonly Ctx ReturnOnly = new Ctx(1);
    public static readonly Ctx CurrentMethod = new Ctx(2);
    public bool IsCallingMethod => _value == 0;
    public bool IsReturnOnly => _value == 1;
    public bool IsConvertibleTo(Ctx other) => this._value <= other._value;
    public Ctx Intersect(Ctx other) => this.IsConvertibleTo(other) ? other : this;
    public override string ToString() => _value switch { 0 => "Calling", 1 => "ReturnOnly", 2 => "Current", _ => $"<{_value}>" };
}
static class P
{
    static Level? FromScope(Ctx lifetime) => lifetime switch
    {
        { IsReturnOnly: true } => Level.ReturnOnly,
        { IsCallingMethod: true } => Level.CallingMethod,
        _ => null,
    };
    static string Check(Ctx c)
    {
        if (FromScope(c) is { } level) return "added " + level;
        return "skipped";
    }
    static void Main()
    {
        Console.WriteLine(Check(Ctx.CallingMethod));
        Console.WriteLine(Check(Ctx.ReturnOnly));
        Console.WriteLine(Check(Ctx.CurrentMethod));
        int? n = null; int? m = 3;
        Console.WriteLine((n is { } a ? "a" + a : "none") + " " + (m is { } b ? "b" + b : "none"));
        Console.WriteLine((n is { }) + " " + (m is { }) + " " + (n is not null) + " " + (m is not null));
        Level? l = null; Level? k = Level.ReturnOnly;
        Console.WriteLine((l is { } x ? x.ToString() : "null") + " " + (k is { } y ? y.ToString() : "null"));
        Console.WriteLine(Ctx.CurrentMethod.Intersect(Ctx.CallingMethod) + " " + Ctx.CallingMethod.Intersect(Ctx.ReturnOnly) + " " + Ctx.CurrentMethod.IsConvertibleTo(Ctx.ReturnOnly));
    }
}
"#,
        "added CallingMethod\nadded ReturnOnly\nskipped\nnone b3\nFalse True False True\nnull ReturnOnly\nCurrent ReturnOnly False\n",
    );
}

#[test]
fn a_ref_parameter_of_a_hosted_closure_is_a_reference_in_its_member_reference() {
    check(
        "hosted_closure_ref_parameters",
        r#"
using System;
using System.Collections.Generic;
static class P
{
    delegate void Adjust(ref int value);
    static string Run<T>(T tag, int start) where T : class
    {
        var log = new List<string>();
        Adjust twice = (ref int v) => { v *= 2; log.Add(tag + ":" + v); };
        int n = start;
        twice(ref n);
        bump(ref n, 5);
        return string.Join(",", log) + " " + n;

        static void bump(ref int value, int by) => value += by;
    }
    static int Outer<T>(T tag, int x) where T : class
    {
        int calls = 0;
        void add(ref int v, int by) { v += by; calls++; }
        add(ref x, 1); add(ref x, 2);
        Func<int> read = () => calls;
        return x * 10 + read();
    }
    static void Main()
    {
        Console.WriteLine(Run("a", 3));
        Console.WriteLine(Outer("b", 4));
    }
}
"#,
        "a:6 11\n72\n",
    );
}

#[test]
fn a_cast_from_a_nullable_reads_the_value_before_converting_it() {
    check(
        "nullable_cast_unwraps",
        r#"
using System;
enum Kind : short { A = 1, B = 2, C = 300 }
static class P
{
    static void Main()
    {
        Kind? k = Kind.C;
        Console.WriteLine((int)k + " " + (long)k + " " + (byte)(Kind?)Kind.B);
        int? n = 7; double? d = 2.5;
        Console.WriteLine((short)n + " " + (int)d + " " + (double)n + " " + (Kind)(int)n);
        try { int? none = null; Console.WriteLine((int)none); }
        catch (InvalidOperationException) { Console.WriteLine("no value"); }
        Kind? m = null;
        Console.WriteLine(m.HasValue ? "has" : "none");
        Console.WriteLine((int)k < 0 || (int)k > 200);
    }
}
"#,
        "300 300 2\n7 2 7 7\nno value\nnone\nTrue\n",
    );
}

#[test]
fn a_static_lambda_in_a_generic_method_of_a_generic_type_is_instantiated() {
    check(
        "generic_method_lambda_in_generic_type",
        r#"
using System;
using System.Threading;
using System.Threading.Tasks;
class Holder<T> { public T Value; public Holder(T v) { Value = v; } }
class Queue<TElement>
{
    public TElement Last;
    public static string Attach<T>(T item)
    {
        var holder = new Holder<T>(item);
        Func<object, string> describe = static s => ((Holder<T>)s).Value.ToString();
        Func<T, Holder<T>> wrap = static v => new Holder<T>(v);
        return describe(holder) + "/" + wrap(item).Value;
    }
    public string Tag<T>(T item) => Run(static (object s) => "tag:" + ((Holder<T>)s).Value + ((Queue<TElement>)null == null), new Holder<T>(item));
    static string Run(Func<object, string> f, object s) => f(s);
}
static class P
{
    static void Main()
    {
        Console.WriteLine(Queue<int>.Attach("x"));
        Console.WriteLine(Queue<string>.Attach(3.5));
        Console.WriteLine(new Queue<int>().Tag(7));
        var tcs = new TaskCompletionSource<int>();
        using var cts = new CancellationTokenSource();
        cts.Token.Register(static s => ((TaskCompletionSource<int>)s).TrySetCanceled(), tcs, false);
        cts.Cancel();
        Console.WriteLine(tcs.Task.IsCanceled);
    }
}
"#,
        "x/x\n3.5/3.5\ntag:7True\nTrue\n",
    );
}

#[test]
fn a_fixed_size_buffer_is_a_struct_of_its_size_and_fixed_pins_its_first_element() {
    check(
        "fixed_size_buffers",
        r#"
using System;
using System.Runtime.InteropServices;
unsafe struct State
{
    public const int Count = 4;
    public fixed ulong Acc[Count];
    public fixed byte Buffer[16];
    public uint Used;
}
static unsafe class P
{
    static void Fill(ref State state)
    {
        fixed (ulong* acc = state.Acc)
        {
            for (int i = 0; i < State.Count; i++) acc[i] = (ulong)(i + 1) * 100;
        }
        fixed (byte* buffer = state.Buffer)
        {
            for (int i = 0; i < 16; i++) buffer[i] = (byte)(i * 3);
        }
        state.Used = 16;
    }
    static ulong Sum(ref State state)
    {
        ulong total = 0;
        fixed (ulong* acc = state.Acc) fixed (byte* buffer = state.Buffer)
        {
            for (int i = 0; i < State.Count; i++) total += acc[i];
            for (int i = 0; i < (int)state.Used; i++) total += buffer[i];
        }
        return total;
    }
    static int First(int[] a) { fixed (int* p = &a[0]) { return *p; } }
    static int Third(ReadOnlySpan<byte> s) { fixed (byte* p = &MemoryMarshal.GetReference(s)) { return p[2]; } }
    static void Main()
    {
        var state = new State();
        Fill(ref state);
        Console.WriteLine(Sum(ref state) + " " + sizeof(State) + " " + state.Used);
        Console.WriteLine(First(new[] { 5, 6 }) + " " + Third(new byte[] { 1, 2, 3 }));
    }
}
"#,
        "1360 56 16\n5 3\n",
    );
}

#[test]
fn a_special_struct_is_stored_through_a_reference_whole() {
    check(
        "special_struct_through_reference",
        r#"
using System;
static class P
{
    static bool Crack(out decimal value, int low, int mid, int high, bool negative, byte scale)
    {
        value = new decimal(low, mid, high, negative, scale);
        return true;
    }
    static void Swap(ref decimal a, ref decimal b) { var t = a; a = b; b = t; }
    static void Point(ref IntPtr p) { p = (IntPtr)42; }
    static void Main()
    {
        Crack(out var d, 12345, 0, 0, true, 2);
        decimal x = 1.5m, y = 2.25m;
        Swap(ref x, ref y);
        IntPtr q = IntPtr.Zero;
        Point(ref q);
        Console.WriteLine(d + " " + x + " " + y + " " + q);
    }
}
"#,
        "-123.45 2.25 1.5 42\n",
    );
}

#[test]
fn explicit_layout_places_fields_where_field_offset_says() {
    check(
        "explicit_layout",
        r#"
using System;
using System.Runtime.InteropServices;
[StructLayout(LayoutKind.Explicit)]
struct FloatUnion
{
    [FieldOffset(0)] public uint IntData;
    [FieldOffset(0)] public float FloatData;
}
[StructLayout(LayoutKind.Explicit, Size = 1)]
readonly struct Tiny
{
    [FieldOffset(0)] private readonly byte _value;
    public Tiny(byte value) { _value = value; }
    public byte Value => _value;
}
[StructLayout(LayoutKind.Sequential, Pack = 1)]
struct Packed { public byte A; public int B; }
static unsafe class P
{
    static void Main()
    {
        var u = new FloatUnion { IntData = 0x3FC00000 };
        Console.WriteLine(u.FloatData);
        u.FloatData = 2.5f;
        Console.WriteLine(u.IntData.ToString("X"));
        Console.WriteLine(new Tiny(7).Value + " " + sizeof(Tiny) + " " + sizeof(Packed) + " " + sizeof(FloatUnion));
    }
}
"#,
        "1.5\n40200000\n7 1 5 4\n",
    );
}

#[test]
fn optional_parameters_carry_their_defaults_in_metadata() {
    check(
        "parameter_defaults",
        r#"
using System;
using System.Reflection;
using System.Threading;
enum Mode { Off, On = 3 }
class Options
{
    public Options(int level = 4, long limit = 5, double scale = 2, string name = "n", Mode mode = Mode.On, bool? flag = null, CancellationToken token = default, float ratio = 1.5f, byte small = 7, object o = null) { }
    public static bool Try(out int value, in long big, ref short s) { value = 1; return true; }
}
static class P
{
    static void Main()
    {
        foreach (var p in typeof(Options).GetConstructors()[0].GetParameters())
            Console.WriteLine(p.Name + " optional=" + p.IsOptional + " hasDefault=" + p.HasDefaultValue + " default=" + (p.DefaultValue ?? "null") + " " + (p.DefaultValue?.GetType().Name ?? "-"));
        foreach (var p in typeof(Options).GetMethod("Try").GetParameters())
            Console.WriteLine(p.Name + " out=" + p.IsOut + " in=" + p.IsIn + " optional=" + p.IsOptional);
        var ctor = typeof(Options).GetConstructors()[0];
        var args = new object[ctor.GetParameters().Length];
        for (int i = 0; i < args.Length; i++) args[i] = ctor.GetParameters()[i].DefaultValue;
        Console.WriteLine(ctor.Invoke(args) != null);
    }
}
"#,
        "level optional=True hasDefault=True default=4 Int32\nlimit optional=True hasDefault=True default=5 Int64\nscale optional=True hasDefault=True default=2 Double\nname optional=True hasDefault=True default=n String\nmode optional=True hasDefault=True default=On Mode\nflag optional=True hasDefault=True default=null -\ntoken optional=True hasDefault=True default=null -\nratio optional=True hasDefault=True default=1.5 Single\nsmall optional=True hasDefault=True default=7 Byte\no optional=True hasDefault=True default=null -\nvalue out=True in=False optional=False\nbig out=False in=True optional=False\ns out=False in=False optional=False\nTrue\n",
    );
}

#[test]
fn a_local_function_whose_variables_a_closure_captures_gets_a_class_per_call() {
    check(
        "recursive_local_function_closures",
        r#"
using System;
using System.Collections.Generic;
class Node { public int Value; public List<Node> Children = new(); public Node(int v, params Node[] kids) { Value = v; Children.AddRange(kids); } }
static class P
{
    static string Describe(Node root)
    {
        var log = new List<string>();
        int depth = 0;
        // A local function whose parameter and local a lambda captures, called recursively.
        static void walk(Node node, Func<string, string>? wrap, List<string> log, ref int depth)
        {
            int level = depth;
            Func<string, string> mine = (string text) =>
            {
                var wrapped = node.Value + "(" + text + ")";
                return wrap?.Invoke(wrapped) ?? wrapped;
            };
            log.Add(mine("L" + level));
            depth++;
            foreach (var child in node.Children) walk(child, mine, log, ref depth);
            depth--;
        }
        walk(root, null, log, ref depth);
        return string.Join(" ", log);
    }
    static int Count(Node root)
    {
        int total = 0;
        void visit(Node n) { total += n.Value; foreach (var c in n.Children) visit(c); }
        visit(root);
        return total;
    }
    static Func<int> Counter(int start)
    {
        Func<int> make(int seed)
        {
            int current = seed;
            return () => ++current;
        }
        var a = make(start); var b = make(start + 100);
        a(); a();
        return () => a() * 1000 + b();
    }
    static void Main()
    {
        var tree = new Node(1, new Node(2, new Node(4)), new Node(3));
        Console.WriteLine(Describe(tree));
        Console.WriteLine(Count(tree));
        Console.WriteLine(Counter(5)());
    }
}
"#,
        "1(L0) 1(2(L1)) 1(2(4(L2))) 1(3(L1))\n10\n8106\n",
    );
}

#[test]
fn a_thread_static_field_is_one_per_thread() {
    check(
        "thread_static",
        r#"
using System;
using System.Threading;
static class P
{
    [ThreadStatic] static int perThread;
    static int shared;
    static Thread Adder(int n)
    {
        var thread = new Thread(() => { perThread += n; Interlocked.Add(ref shared, n); });
        thread.Start();
        return thread;
    }
    static void Main()
    {
        perThread = 100; shared = 100;
        var threads = new Thread[4];
        for (int i = 0; i < 4; i++) threads[i] = Adder(i + 1);
        foreach (var t in threads) t.Join();
        Console.WriteLine(perThread + " " + shared);
        var worker = new Thread(() => Console.WriteLine("worker sees " + perThread));
        worker.Start(); worker.Join();
    }
}
"#,
        "100 110\nworker sees 0\n",
    );
}

#[test]
fn an_unsigned_integer_widens_without_a_sign() {
    check(
        "unsigned_widening",
        r#"
using System;
static class P
{
    static string Emit(long value)
    {
        if (unchecked((int)value) == value) return "i4+conv.i8";
        else if (unchecked((uint)value) == value) return "i4+conv.u8";
        else return "i8";
    }
    static void Main()
    {
        long v = 2147483648L;
        int i = unchecked((int)v); uint u = unchecked((uint)v);
        Console.WriteLine((i == v) + " " + (u == v) + " " + (v == i) + " " + (v == u) + " " + (i < v) + " " + (u > 5L));
        Console.WriteLine(Emit(5) + " " + Emit(2147483648L) + " " + Emit(-1) + " " + Emit(1L << 40) + " " + Emit(4294967295L));
        ulong big = 1UL << 63; int neg = -1;
        Console.WriteLine(Q.Floats());
        Console.WriteLine((big > 0) + " " + (u < big) + " " + (i == -1L) + " " + ((long)u) + " " + ((ulong)u) + " " + (neg == 4294967295L));
    }
}
static class Q
{
    public static string Floats()
    {
        uint u = 3000000000; ulong big = 18000000000000000000UL;
        double d = u; float f = u; double e = big;
        return d + " " + f + " " + e + " " + (double)(u + 5) + " " + (long)u;
    }
}
"#,
        "False True False True True True\ni4+conv.i8 i4+conv.u8 i4+conv.i8 i8 i4+conv.u8\n3000000000 3E+09 1.8E+19 3000000005 3000000000\nTrue True False 2147483648 2147483648 False\n",
    );
}

#[test]
fn a_loop_body_variable_a_closure_captures_is_fresh_each_time_round() {
    check(
        "loop_body_captures",
        r#"
using System;
using System.Collections.Generic;
static class P
{
    static void Main()
    {
        var fs = new List<Func<string>>();
        foreach (var word in new[] { "a", "b", "c" }) fs.Add(() => word);
        for (int i = 0; i < 3; i++) { int j = i * 10; fs.Add(() => j + ""); }
        for (int i = 0; i < 2; i++) fs.Add(() => "i" + i);
        int k = 0; string prefix = "p";
        while (k < 2) { var local = prefix + k; fs.Add(() => local + "/" + k); k++; }
        var list = new List<int> { 5, 6 };
        foreach (var n in list) { int twice = n * 2; fs.Add(() => n + ":" + twice); }
        Console.WriteLine(string.Join(" ", fs.ConvertAll(f => f())));
        int total = 0;
        foreach (var n in list) { Action add = () => total += n; add(); }
        Console.WriteLine(total);
    }
}
"#,
        "a b c 0 10 20 i2 i2 p0/2 p1/2 5:10 6:12\n11\n",
    );
}

#[test]
fn ref_locals_and_spans_live_between_awaits_and_yields() {
    check(
        "ref_between_suspensions",
        r#"
using System;
using System.Collections.Generic;
using System.Threading.Tasks;
class C { public Buffer4<int> F; public readonly Buffer4<int> R = default; }
[System.Runtime.CompilerServices.InlineArray(4)]
public struct Buffer4<T> { private T _element0; }
static class P
{
    static async Task<int> Sum(int[] values)
    {
        await Task.Yield();
        Span<int> span = values;
        ref int first = ref span[0];
        first += 100;
        int total = 0;
        foreach (var v in span) total += v;
        await Task.Delay(1);
        return total;
    }
    static IEnumerable<int> Walk(C c)
    {
        foreach (var v in c.F) { c.F[3] = 7; yield return v; }
        foreach (var v in c.R) yield return v;
    }
    static async Task<int> Element(C c) => c.F[await Task.FromResult(^1)];
    static async Task Walk2(C c)
    {
        foreach (var v in c.F) { Console.Write(v + ";"); await Task.Yield(); }
        Console.WriteLine();
    }
    static void Main()
    {
        Console.WriteLine(Sum(new[] { 1, 2, 3 }).Result);
        var c = new C();
        c.F[0] = 1;
        Console.WriteLine(string.Join(",", Walk(c)));
        Console.WriteLine(Element(c).Result);
        Walk2(c).Wait();
    }
}
"#,
        "106\n1,0,0,7,0,0,0,0\n7\n1;0;0;7;\n",
    );
}

#[test]
fn a_ref_conditional_is_a_variable_to_write_read_and_await_around() {
    check(
        "ref_conditional",
        r#"
using System;
using System.Threading.Tasks;
class C
{
    int F;
    struct S { public int x; }
    static int x, y;
    static S s1, s2;
    static ref int Pick(bool b) => ref (b ? ref s1 : ref s2).x;
    static async Task<C> Later(C c) { await Task.Yield(); return c; }
    static async Task Assign(bool b, C c1, C c2)
    {
        (b ? ref (await Later(c1)).F : ref c2.F) = 5;
    }
    static void Main()
    {
        bool b = true;
        ((b) ? ref x : ref y) = 1;
        b = false;
        (b ? ref x : ref y)++;
        Console.WriteLine(x + " " + y + " " + (b ? ref x : ref y));
        Pick(true)++;
        Console.WriteLine(s1.x + " " + s2.x);
        var c1 = new C(); var c2 = new C();
        Assign(true, c1, c2).Wait();
        Assign(false, c1, c2).Wait();
        Console.WriteLine(c1.F + " " + c2.F);
    }
}
"#,
        "1 1 1\n1 0\n5 5\n",
    );
}

#[test]
fn pointer_member_access_and_fixed_buffers() {
    check(
        "pointer_members",
        r#"
using System;
unsafe struct S
{
    public int x;
    public fixed int buffer[4];
    public int Twice() => x * 2;
}
class Holder { public S s; public readonly S ro; }
static class P
{
    static unsafe void Main()
    {
        S s = default;
        S* p = &s;
        p->x = 21;
        p->x++;
        Console.WriteLine(p->x + " " + p->Twice());
        s.buffer[2] = 7;
        int* b = s.buffer;
        b[3] = b[2] + 1;
        Console.WriteLine(s.buffer[3]);
        var h = new Holder();
        h.s.buffer[1] = 5;
        fixed (int* q = h.ro.buffer) { q[0] = 9; }
        Console.WriteLine(h.s.buffer[1] + " " + h.ro.buffer[0]);
    }
}
"#,
        "22 44\n8\n5 9\n",
    );
}

#[test]
fn pointer_offsets_widen_by_their_signedness() {
    check(
        "pointer_offsets",
        r#"
using System;
unsafe static class P
{
    delegate int D();
    static void Main()
    {
        byte* data = (byte*)0x76543210;
        uint offset = 0x80000000;
        Console.WriteLine("{0:X}", (ulong)(data + offset));
        byte* two = (byte*)2;
        checked { two = two + 2147483649; }
        Console.WriteLine((long)two);
        try { checked { int back = -1; two = two + back; } }
        catch (OverflowException) { Console.WriteLine("overflow"); }
        int* v = stackalloc int[1];
        *v = 7;
        D d = delegate { return *v; };
        int*[] pointers = { (int*)1, (int*)2 };
        foreach (var p in pointers) Console.Write((int)p);
        Console.WriteLine(" " + d());
    }
}
"#,
        "F6543210\n2147483651\noverflow\n12 7\n",
    );
}

#[test]
fn ref_fields_and_stackalloc_as_an_argument() {
    check(
        "ref_fields",
        r#"
using System;
ref struct R
{
    public ref int F;
    public ref byte G = ref Pick(stackalloc byte[1]);
    public R(ref int x) { F = ref x; }
    static ref byte Pick(scoped Span<byte> s) => ref shared;
    public static byte shared = 3;
}
struct S
{
    public static implicit operator int(S? s) => s.HasValue ? 1 : 0;
}
static class P
{
    static int Length(Span<byte> s) => s.Length;
    static void Main()
    {
        int a = 1;
        var r = new R(ref a);
        r.F = 5;
        a++;
        R.shared = 4;
        Console.WriteLine(a + " " + r.F + " " + r.G + " " + Length(stackalloc byte[2]));
        S? none = null;
        int n = none, one = (S?)new S();
        Console.WriteLine(n + " " + one);
    }
}
"#,
        "6 6 4 2\n0 1\n",
    );
}

#[test]
fn a_lambda_outside_unsafe_code_does_not_take_a_pointer() {
    check(
        "safe_lambda",
        r#"
using System;
unsafe delegate void F1(int* x);
delegate void F2(int x);
static class P
{
    static void Go(F1 f) => Console.Write(1);
    static void Go(F2 f) => Console.Write(2);
    static void Main()
    {
        Go(x => { });
        Console.WriteLine();
    }
}
"#,
        "2\n",
    );
}

#[test]
fn fixed_pins_what_get_pinnable_reference_hands_back() {
    check(
        "pattern_fixed",
        r#"
using System;
using System.Collections;
class Fixable { public int[] data = { 1, 2, 3 }; public ref int GetPinnableReference() => ref data[0]; }
struct Bag : IEnumerable { public int n; public IEnumerator GetEnumerator() => null; }
static class Ext
{
    public static ref int GetPinnableReference<T>(this T value) => ref (new int[] { 7, 8 })[0];
    public static void Add(ref this Bag bag, int value) { bag.n += value; }
}
static class P
{
    static unsafe int Second<T>(T value) { fixed (int* p = value) { return p == null ? -1 : p[1]; } }
    static unsafe void Main()
    {
        fixed (int* p = new Fixable()) Console.Write(p[2] + " ");
        Fixable none = null;
        fixed (int* p = none) Console.Write((p == null) + " ");
        Console.WriteLine(Second(1) + " " + Second<object>(null) + " " + Second<int?>(null));
        var grid = new int[2, 2];
        fixed (int* p = grid) p[3] = 4;
        var bag = new Bag { 1, 2, 3 };
        Console.WriteLine(grid[1, 1] + " " + bag.n);
    }
}
"#,
        "3 True 8 -1 -1\n4 6\n",
    );
}

#[test]
fn spans_walked_by_index_and_arguments_in_written_order() {
    check(
        "spans_and_argument_order",
        r#"
using System;
[System.Runtime.CompilerServices.InlineArray(3)]
struct Buffer3
{
    private int _element0;
    public Buffer3() { this[0] = 1; this[^1] = 3; }
    public int this[int i] => -1;
    public int Length => 99;
}
static class P
{
    static int Log(string what, int value) { Console.Write(what); return value; }
    static void M(int a, int b) => Console.WriteLine(" " + a + b);
    static void R(int a, ref int b) => Console.WriteLine(" " + a + b);
    static void Main()
    {
        int[] data = { 1, 2, 3 };
        foreach (ref int d in data.AsSpan()) d *= 10;
        foreach (ref readonly int d in (ReadOnlySpan<int>)data) Console.Write(d + ";");
        var b = new Buffer3();
        Console.WriteLine(" " + b[0] + b[1] + b[^1]);
        M(b: Log("b", 2), a: Log("a", 1));
        int x = 1, y = 2;
        ref int z = ref x;
        R(b: ref z, a: (z = ref y));
        int v = (z = ref x);
        Console.WriteLine(v);
    }
}
"#,
        "10;20;30; 103\nba 12\n 21\n1\n",
    );
}

#[test]
fn references_returned_by_lambdas_groups_and_calls() {
    check(
        "ref_returns",
        r#"
using System;
using System.Threading.Tasks;
delegate ref T D<T>();
class Box<T> { T value; public ref T Get() => ref value; }
class Base { } class Derived : Base { } class Leaf : Derived { }
struct S { public int f; }
static class P
{
    delegate ref Base RefBase(Leaf leaf);
    static Base shared = new Base();
    static ref Base Pick(Base b) => throw null;
    static ref Base Pick(Derived d) => ref shared;
    static string Mode(ref readonly int i) => "ref readonly";
    static string Mode(int i) => "plain";
    static ref readonly S Bump(ref S s) { s.f++; return ref s; }
    static void Show(in int a, in int b) => Console.Write(a + "" + b + " ");
    static async Task<int> Later(int v) { await Task.Yield(); return v; }
    static async Task Spill()
    {
        var s = new S();
        Show(Bump(ref s).f, await Later(9));
        Console.WriteLine(s.f);
    }
    static void Main()
    {
        var box = new Box<int>();
        D<int> d = () => ref box.Get();
        d() = 4;
        D<int> group = box.Get;
        group() += 1;
        RefBase pick = Pick;
        Console.WriteLine(box.Get() + " " + (pick(null) == shared) + " " + Mode(1));
        var s = new S();
        Show(Bump(ref s).f, Bump(ref s).f);
        Spill().Wait();
    }
}
"#,
        "5 True plain\n22 19 1\n",
    );
}

#[test]
fn an_in_parameter_crosses_into_another_assembly_the_way_it_was_declared() {
    // `in` on a virtual member, an interface's and an indexer's: the first
    // two are under `modreq(InAttribute)`, and a call or an override from
    // the other assembly has to say so or it names nothing.
    check_with_library(
        "InAcross",
        r#"
public class Parent
{
    public virtual void M(in int p) { System.Console.Write("P" + p); }
    public int this[in int p] { get { return p * 10; } set { System.Console.Write("S" + p); } }
}
public interface IShape
{
    int Area(in int scale);
}
public readonly struct Point
{
    public readonly int X;
    public Point(int x) { X = x; }
    public int Twice() => X * 2;
}
public struct Counter
{
    public int Count;
    public void Bump() { Count++; }
}
"#,
        r#"
class Child : Parent
{
    public override void M(in int p) { System.Console.Write("C" + p); }
}
class Square : IShape
{
    // Not virtual: the interface's slot is answered by a private method with
    // the interface's signature that calls this one.
    public int Area(in int scale) => 4 * scale;
}
class Program
{
    static void Show(in Counter counter)
    {
        // A call on an `in` parameter changes a copy.
        counter.Bump();
        System.Console.Write(" " + counter.Count);
    }
    static void Main()
    {
        int value = 5;
        Parent parent = new Child();
        parent.M(value);
        parent[value] = 1;
        System.Console.Write(" " + parent[value]);
        IShape shape = new Square();
        System.Console.Write(" " + shape.Area(3));
        System.Console.Write(" " + new Point(21).Twice());
        Show(new Counter());
    }
}
"#,
        "C5S5 50 12 42 0",
    );
}

#[test]
fn a_dynamic_value_is_bound_when_the_program_runs() {
    // Every operation on `dynamic` goes through a call site the C# runtime
    // binder makes on first use: members, calls, indexers, operators,
    // conversions, and the overload a `dynamic` argument picks.
    check(
        "DynamicSites",
        r#"
using System;
using System.Collections.Generic;
class Point { public int X; public int Y { get; set; } public int Sum(int a) => X + Y + a; }
class Program
{
    static string Kind(int x) => "int";
    static string Kind(string x) => "string";
    static void Main()
    {
        dynamic d = 3;
        Console.Write(d + 4);
        Console.Write(" " + Kind(d) + " " + Kind((dynamic)"s"));
        dynamic p = new Point();
        p.X = 5;
        p.Y++;
        p.X += 10;
        Console.Write(" " + p.Sum(1));
        dynamic list = new List<int> { 1, 2 };
        list[0] += 100;
        foreach (var item in list) Console.Write(" " + item);
        int n = d;
        n += d;
        Console.Write(" " + n);
        if (d > 2 && d < 4) Console.Write(" yes");
        dynamic made = new Point();
        Console.Write(" " + (made.X ?? 0));
        Func<dynamic, dynamic> twice = x => x * 2;
        Console.Write(" " + twice(21));
        try { throw (dynamic)"no"; } catch (Exception e) { Console.Write(" " + e.GetType().Name); }
        // A struct with a home is passed to the site as the variable it is.
        Counter counter = new Counter();
        counter.Add(d);
        Console.Write(" " + counter.N);
        // An initializer on an element the runtime binder finds.
        var holder = new Holder { [d - 2] = { F = 7 } };
        Console.Write(" " + holder.Items[1].F);
    }
}
struct Counter { public int N; public void Add(int k) { N += k; } }
class Item { public int F; }
class Holder { public Item[] Items = { new Item(), new Item() }; public Item this[int i] => Items[i]; }
"#,
        "7 int string 17 101 2 6 yes 0 42 RuntimeBinderException 3 7",
    );
}

#[test]
fn reflection_sees_an_indexer_beside_an_event() {
    // `MethodSemantics` is sorted by what it associates, or the runtime's
    // binary search misses the property; and an indexer is named by the
    // type's `[DefaultMember]`.
    check(
        "IndexerBesideEvent",
        r#"
using System;
class S
{
    public event Action E;
    public void Fire() => E?.Invoke();
    public int this[int a, int b] => a * 10 + b;
}
class Program
{
    static void Main()
    {
        foreach (var property in typeof(S).GetProperties())
            Console.Write(property.Name + property.GetIndexParameters().Length);
        foreach (var attribute in typeof(S).GetCustomAttributes(false))
            Console.Write(" " + ((System.Reflection.DefaultMemberAttribute)attribute).MemberName);
    }
}
"#,
        "Item2 Item",
    );
}

#[test]
fn dynamic_in_a_signature_crosses_into_another_assembly() {
    // `dynamic` is `object` in metadata with `[Dynamic]` saying which one;
    // the other assembly reads it back and binds what it does with the value
    // at run time. A field-like event is invoked inside its class.
    check_with_library(
        "DynamicAcross",
        r#"
using System;
using System.Collections.Generic;
public class Source
{
    public dynamic Get() => "text";
    public List<dynamic> Items = new List<dynamic> { 1, "two" };
    public event Action<dynamic> Raised;
    public void Raise() => Raised(this);
    public string Name => "source";
}
"#,
        r#"
class Program
{
    static void Main()
    {
        var source = new Source();
        System.Console.Write(source.Get().Length);
        System.Console.Write(" " + source.Items[1].ToUpper());
        source.Raised += s => System.Console.Write(" " + s.Name);
        source.Raise();
    }
}
"#,
        "4 TWO source",
    );
}

#[test]
fn tuple_element_names_cross_into_another_assembly() {
    // `ValueTuple<...>` cannot carry the names of a tuple's elements, so
    // `[TupleElementNames]` does, and the other assembly names them again.
    check_with_library(
        "TupleNamesAcross",
        r#"
using System.Collections.Generic;
public class Source
{
    public (int count, string name) Get() => (2, "pair");
    public List<(int x, (string a, string b) inner)> Items = new List<(int, (string, string))> { (1, ("p", "q")) };
    public (int first, int) Partial { get; } = (5, 6);
    public static int Sum((int left, int right) pair) => pair.left + pair.right;
}
"#,
        r#"
class Program
{
    static void Main()
    {
        var source = new Source();
        var got = source.Get();
        System.Console.Write(got.count + got.name);
        System.Console.Write(" " + source.Items[0].inner.b + source.Items[0].x);
        System.Console.Write(" " + source.Partial.first + source.Partial.Item2);
        System.Console.Write(" " + Source.Sum((left: 3, right: 4)));
    }
}
"#,
        "2pair q1 56 7",
    );
}

#[test]
fn a_method_group_with_a_string_parameter_is_no_delegate_of_dynamic() {
    // A delegate hands its `dynamic` argument on by identity or reference
    // conversion, which only `object` has: `F(string)` is an `In<string>`.
    check(
        "GroupContravariance",
        r#"
delegate void In<in T>(T t);
class Program
{
    static void F(string s) { }
    static void M(In<dynamic> f) { System.Console.Write('A'); }
    static void M(In<string> f) { System.Console.Write('B'); }
    static void G(object o) { }
    static void Main()
    {
        M(F);
        In<dynamic> g = G;
        g(1);
        System.Console.WriteLine();
    }
}
"#,
        "B\n",
    );
}

#[test]
fn a_switch_goes_through_the_one_conversion_to_a_type_it_can_switch_on() {
    check(
        "switch_governing_conversion",
        r#"
using System;
class Conv
{
    public static implicit operator int(Conv c) { return 1; }
}
struct Half
{
    public static implicit operator string(Half h) { Console.Write("[conv]"); return "h"; }
}
static class P
{
    static string Which(long? x)
    {
        switch (x) { case null: return "null"; case 1: return "one"; case > 5: return "big"; default: return "other"; }
    }
    static void Main()
    {
        switch (new Conv()) { case 1: Console.WriteLine("one"); break; default: Console.WriteLine("fail"); break; }
        Half? some = new Half(), none = null;
        switch (some) { case "h": Console.WriteLine("h"); break; }
        switch (none) { case null: Console.WriteLine("none"); break; }
        Console.WriteLine(Which(null) + " " + Which(1) + " " + Which(9) + " " + Which(3));
    }
}
"#,
        "one\n[conv]h\nnone\nnull one big other\n",
    );
}

#[test]
fn a_loop_condition_variable_a_closure_captures_is_fresh_each_time_round() {
    check(
        "loop_condition_captures",
        r#"
using System;
using System.Collections.Generic;
static class P
{
    static bool Take(int y, out int x) { x = y; return true; }
    static bool Log(bool go, int shown) { Console.Write(shown + " "); return go; }
    static void Main()
    {
        var fs = new List<Func<string>>();
        int f = 1;
        while (Take(f, out var w) && f < 3) { fs.Add(() => "w" + w); f++; }
        f = 1;
        do { } while (Take(f++, out var d) && Log(f < 3, d) && fs.Count > 0 && Add(fs, () => "d" + d));
        for (Take(1, out var i); Take(i * 10, out var c) && i < 3; i++) fs.Add(() => i + "/" + c);
        for (Log(true, 7); Log(false, 8); ) { }
        Console.WriteLine();
        Console.WriteLine(string.Join(" ", fs.ConvertAll(g => g())));
    }
    static bool Add(List<Func<string>> fs, Func<string> g) { fs.Add(g); return true; }
}
"#,
        "1 2 7 8 \nw1 w2 d1 3/10 3/20\n",
    );
}

#[test]
fn a_tuple_converts_element_by_element_and_through_operators_on_tuples() {
    check(
        "tuple_conversions",
        r#"
using System;
class C1
{
    public byte X;
    public static explicit operator C1((long, long) arg) { return new C1 { X = (byte)arg.Item2 }; }
    public static explicit operator (byte, byte)(C1 arg) { return (arg.X, 2); }
}
class Two
{
    public int V;
    public static explicit operator Two(int v) { return new Two { V = v + 1 }; }
    public override string ToString() { return "T" + V; }
}
struct AA
{
    public static implicit operator AA((int X1, int Y1) x) { Console.Write(x + ";"); return new AA(); }
}
static class P
{
    static void Take(AA? value) { }
    static void Main()
    {
        var x = (1, 7);
        C1 c = (C1)x;
        (int, int)? back = ((int, int)?)c;
        Console.WriteLine(back);
        var twos = ((Two, Two))x;
        Console.WriteLine(twos);
        var wide = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
        (long, long, long, long, long, long, long, long, long, long) widened = wide;
        Console.WriteLine(widened.Item10 + widened.Item1);
        var bytes = ((byte, byte, byte, byte, byte, byte, byte, byte, byte, byte))widened;
        Console.WriteLine(bytes);
        Take((3, 4));
        AA? made = x;
        Console.WriteLine();
    }
}
"#,
        "(7, 2)\n(T2, T8)\n11\n(1, 2, 3, 4, 5, 6, 7, 8, 9, 10)\n(3, 4);(1, 7);\n",
    );
}

#[test]
fn operators_on_a_nullable_are_lifted() {
    check(
        "lifted_operators",
        r#"
using System;
struct S
{
    public int X;
    public S(int x) { X = x; }
    public static S operator ++(S s) { return new S(s.X + 1); }
    public static int operator -(S s) { return -s.X; }
    public static implicit operator S((int, int) t) { return new S(t.Item1 + t.Item2); }
}
enum E : short { Zero, One }
struct Point
{
    public static implicit operator int(Point p) { Console.Write("[int]"); return 0; }
}
class Money
{
    public static implicit operator Money(decimal value) { Console.Write("[m" + value + "]"); return new Money(); }
}
struct Level
{
    public static bool operator >(Level l, int n) { Console.Write(">"); return true; }
    public static bool operator <(Level l, int n) { return false; }
}
struct Dec
{
    public static implicit operator Dec?(decimal d) { Console.Write("[" + d + "]"); return new Dec(); }
}
static class P
{
    static string Show(bool? b) { return b.HasValue ? b.Value.ToString() : "null"; }
    static void Take((byte, int)? t) { Console.Write(t + ";"); }
    static void Main()
    {
        int? n = 1; int a = 2; short? d = 5; int? none = null;
        n += a; n += d; none += a;
        Console.WriteLine(n + " " + none.HasValue);
        S? s = new S(1); S plain = new S(5);
        var old = s++;
        Console.WriteLine(old.Value.X + " " + s.Value.X + " " + (++plain).X + " " + (-s) + " " + (plain++).X);
        S? gone = null; gone++;
        Console.WriteLine(gone.HasValue + " " + (-gone).HasValue);
        E? e = 0; e++; E? ne = null; ne--;
        Console.WriteLine(e + " " + ne.HasValue);
        bool? t = true, f = false, u = null;
        Console.WriteLine(Show(f & u) + " " + Show(t & u) + " " + Show(t | u) + " " + Show(f | u) + " " + Show(true & null));
        (int, int)? pair = (3, 4), nothing = null;
        S? fromPair = pair, fromNothing = nothing;
        Console.WriteLine(fromPair.Value.X + " " + fromNothing.HasValue);
        Take((1, 2));
        Point? here = new Point(), gone2 = null;
        Console.Write((here ?? -1) + ";" + (gone2 ?? -1));
        int? five = 5, nothing2 = null;
        Dec? viaCast = (Dec)five, liftedNull = (Dec?)nothing2;
        Console.Write(";" + viaCast.HasValue + liftedNull.HasValue);
        Money m1 = five, m2 = nothing2;
        Level? level = new Level(), noLevel = null;
        Console.Write(";" + (m2 == null) + (level > 1) + (noLevel > 1));
        Console.WriteLine();
    }
}
"#,
        "8 False\n1 2 6 -2 6\nFalse False\nOne False\nFalse null True null null\n7 False\n(1, 2);[int]0;-1[5];TrueFalse[m5]>;TrueTrueFalse\n",
    );
}

#[test]
fn a_deconstruction_reaches_an_extension_deconstruct_and_converts_the_parts() {
    check(
        "extension_deconstruct",
        r#"
using System;
class C { }
struct V { }
class Box<T> { public T Value; }
class Conv
{
    public static implicit operator int(Conv c) { Console.Write("[conv]"); return 0; }
}
static class D
{
    public static void Deconstruct(this C value, out int a, out string b) { a = 1; b = "one"; }
    public static void Deconstruct(this in V value, out int a, out int b) { a = 2; b = 3; }
    public static void Deconstruct<T>(this Box<T> box, out int a, out T b) { a = 4; b = box.Value; }
    public static void Deconstruct(this char c, out int a, out int b) { a = b = c - '0'; }
}
static class P
{
    static void Main()
    {
        long x; string y;
        (x, y) = new C();
        var (p, q) = new V();
        var (r, s) = new Box<string> { Value = "boxed" };
        Console.WriteLine(x + y + p + q + r + s);
        foreach (var (a, b) in "12") Console.Write(a + b);
        foreach (var (a, b) in new (int, int)[,] { { (1, 2) }, { (3, 4) } }) Console.Write(a * b);
        (int _, var z) = (new Conv(), 5);
        Console.WriteLine(z);
        (Make(out var made).Value, made) = (1, made);
        Console.WriteLine(made);
    }
    class Holder { public int Value { set { Console.Write("set " + value + ";"); } } }
    static Holder Make(out int n) { n = 42; return new Holder(); }
}
"#,
        "1one234boxed\n24212[conv]5\nset 1;42\n",
    );
}

#[test]
fn a_conditional_access_takes_a_compound_assignment_and_a_lock_shares_its_scope() {
    check(
        "conditional_compound",
        r#"
using System;
class C
{
    int f; string s;
    static string held;
    public ref string R(string s) { Console.Write("R(" + s + ")"); return ref held; }
    static void R(C c) { Console.Write(((c?.R("a") = "b") ?? "none") + ";"); }
    static bool Take<T>(T y, out T x) { x = y; return true; }
    static void M(C c)
    {
        c?.f += 1;
        Console.Write((c?.f += 3) ?? 9);
        Console.Write(" " + ((c?.s ??= "set") ?? "none") + ";");
    }
    static void Main()
    {
        M(new C()); M(null);
        R(new C()); R(null);
        lock ((object)Take("locked", out var got)) { }
        Console.WriteLine(" " + got);
    }
}
"#,
        "4 set;9 none;R(a)b;none; locked\n",
    );
}

#[test]
fn an_override_restates_inherited_constraints_and_a_long_tuple_may_be_spelled_as_value_tuple() {
    check(
        "override_constraints_long_tuple",
        r#"
using System;
using System.Collections.Generic;
abstract class Base<T> { public abstract U Echo<U>(U value) where U : T; }
abstract class Middle<T> : Base<List<T>> { }
class Leaf : Middle<int> { public override U Echo<U>(U value) { return value; } }
class Holder<T> { public static int Count { get; set; } }
static class P
{
    static ValueTuple<int, int, int, int, int, int, int, ValueTuple<int, int>> Long()
        => (1, 2, 3, 4, 5, 6, 7, 8, 9);
    static void Main()
    {
        Console.WriteLine(new Leaf().Echo(new List<int> { 1, 2 }).Count);
        Holder<string>.Count = 3;
        Holder<string>.Count += 4;
        Console.WriteLine(Holder<string>.Count);
        var l = Long();
        Console.WriteLine(l.Item9 + l.Item1);
        ValueType boxed = (2, "s");
        Console.WriteLine(boxed);
    }
}
"#,
        "2\n7\n10\n(2, s)\n",
    );
}

#[test]
fn an_initializer_declares_locals_of_its_own() {
    check(
        "initializer_locals",
        r#"
using System;
class P
{
    static bool Take(int y, out int x) { x = y; return true; }
    static int Twice(int x) { return x * 2; }
    static int Seen = Take(21, out var s) ? Twice(s) : 0;
    static int Later = Take(9, out var l) ? ((Func<int>)(() => l + 1))() : 0;
    int Held = Take(4, out var h) ? ((Func<int>)(() => h * 10))() : 0;
    int own = Take(5, out int o) && o > 1 ? o : -1;
    string Text { get; } = 7 is var seven ? "t" + seven : "";
    P(object a, int b) { Console.WriteLine(b); }
    P() : this(Take(3, out var x) ? null : null, ((Func<int>)(() => x + 1))()) { Console.WriteLine(x + " " + own + " " + Text); }
    static void Main() { Console.WriteLine(Seen + " " + Later); Console.WriteLine(new P().Held); }
}
"#,
        "42 10\n4\n3 5 t7\n40\n",
    );
}

#[test]
fn a_condition_goes_through_a_conversion_to_bool_or_operator_true() {
    check(
        "user_defined_conditions",
        r#"
using System;
class Base { public static implicit operator bool(Base b) => true; }
class Derived : Base { }
struct Truthy
{
    int n;
    public Truthy(int n) { this.n = n; }
    public static bool operator true(Truthy t) => t.n > 0;
    public static bool operator false(Truthy t) => t.n <= 0;
}
class Small
{
    public string Text;
    public static implicit operator Small(byte b) => new Small { Text = "b" + b };
}
class Counter
{
    public short N;
    public static implicit operator short(Counter c) => c.N;
    public static implicit operator Counter(short n) => new Counter { N = n };
}
static class P
{
    static void Main()
    {
        if (new Derived()) Console.Write("derived ");
        int count = 3;
        while (new Truthy(count)) count--;
        Console.Write(count + " ");
        Console.Write(new Truthy(1) ? "yes " : "no ");
        Small s = 7;
        Console.Write(s.Text + " ");
        Counter c = (short)5;
        var before = c++;
        ++c;
        Console.WriteLine(before.N + " " + c.N);
    }
}
"#,
        "derived 0 yes b7 5 7\n",
    );
}

#[test]
fn a_match_reads_each_property_once() {
    check(
        "pattern_shared_reads",
        r#"
using System;
class Box
{
    int f;
    public Box(int f) { this.f = f; }
    public int F { get { Console.Write("F "); return f; } }
}
static class P
{
    static bool Test((object, int) u) => u is (Box { F: 1 }, 2) or (Box { F: 1 or 2 }, 1);
    static string Arm(Box b) => b switch { { F: 1 } => "one", { F: 2 } => "two", _ => "other" };
    static void Main()
    {
        Console.WriteLine(Test((new Box(1), 1)));
        Console.WriteLine(Test((new Box(3), 2)));
        Console.WriteLine(Arm(new Box(2)));
        switch (new Box(5)) { case { F: 1 }: break; case { F: > 4 }: Console.WriteLine("big"); break; }
    }
}
"#,
        "F True\nF False\nF two\nF big\n",
    );
}

#[test]
fn a_default_argument_of_a_generic_nullable_is_the_callers_default() {
    check(
        "generic_nullable_default",
        r#"
using System;
static class P
{
    static void M<T>(T? a = default, T? b = default(T?), int? c = (default), int? d = default(byte)) where T : struct
    {
        Console.WriteLine(a.HasValue + " " + b.HasValue + " " + c.HasValue + " " + d);
    }
    static bool Unbound<T>() => typeof(T).GetGenericTypeDefinition() == typeof(Box<>);
    static void Main() { M<long>(); M<long>(1); Console.WriteLine(Unbound<Box<int>>()); }
}
class Box<T> where T : struct { }
"#,
        "False False False 0\nTrue False False 0\nTrue\n",
    );
}

#[test]
fn a_field_like_event_is_called_and_deconstructed_into_where_it_is_declared() {
    check(
        "event_invocation",
        r#"
using System;
class C
{
    static event Action E;
    event Action<int> F;
    static event Func<int> G = () => 7;
    event Func<int> H = () => 8;
    static void Handler() { Console.Write("handled "); }
    static void Main()
    {
        Console.Write(G() + new C().H() + " ");
        (E, _) = (null, 1);
        Console.Write((E == null) + " ");
        (E, _) = (Handler, 1);
        E();
        var c = new C();
        c.F += n => Console.Write(n + " ");
        c.F(1);
        c?.F(2);
        C none = null;
        none?.F(3);
        Console.WriteLine();
    }
}
"#,
        "15 True handled 1 2 \n",
    );
}

#[test]
fn patterns_and_foreach_find_what_the_language_says_they_find() {
    check(
        "pattern_lookups",
        r#"
using System;
using System.Collections.Generic;
class Bag
{
    internal IEnumerator<int> GetEnumerator() { throw null; }
}
class Point { public int Length => 5; }
static class Extensions
{
    public static IEnumerator<int> GetEnumerator(this Bag bag) { yield return 1; yield return 2; }
    public static void Deconstruct(this Point p, out int x, out int y) { x = 3; y = 4; }
    public static string Kind(this FormattableString s) => "formattable";
    public static string Kind(this object o) => "object";
    public static IEnumerator<int> GetEnumerator(this object o) { yield return 7; }
    public static IEnumerator<int> GetEnumerator(this Counted c, int start = 8, params int[] more) { yield return start + more.Length; }
}
struct Boxed { }
class Counted { }
static class P
{
    static string Which<TBase, TDerived>(TBase o) where TDerived : TBase
    {
        switch (o)
        {
            case TDerived: return "derived";
            case TBase: return "base";
            default: return "neither";
        }
    }
    static void Main()
    {
        foreach (var n in new Bag()) Console.Write(n);
        foreach (var n in new Boxed()) Console.Write(n);
        foreach (var n in new Counted()) Console.Write(n);
        const string none = null;
        Console.WriteLine(((string)null) is none);
        Console.WriteLine(new Point() is (3, 4) { Length: 5 });
        Console.WriteLine(Which<object, int>(1) + " " + Which<object, int>("s") + " " + Which<object, int>(null));
        Console.WriteLine($" ".Kind());
    }
}
"#,
        "1278True\nTrue\nderived base neither\nobject\n",
    );
}

#[test]
fn overloads_tie_break_in_the_order_roslyn_asks() {
    check(
        "overload_tie_breaks",
        r#"
using System;
static class P
{
    static void Method(in int x, int op1 = 0, int op2 = 0) => Console.Write("in ");
    static void Method(int x, int op1 = 0, int op2 = 0, int op3 = 0) => Console.Write("val ");
    static void M1(object o, object o1, string s, object o2 = null) => Console.Write("four ");
    static void M1(string s, object o1, object o2) => Console.Write("three ");
    static void Main()
    {
        int x = 1;
        Method(x);
        Method(in x);
        Method(x, 0);
        M1("M", null, null);
        int[] a = new int[default];
        int[] b = { 7 };
        Console.Write(a.Length + " " + b[default] + " ");
        try { throw new Exception(); } catch when (default) { } catch { Console.Write("caught"); }
    }
}
"#,
        "val in val three 0 7 caught",
    );
}

#[test]
fn a_destructor_chains_to_the_base_finalizer_in_a_finally() {
    check(
        "destructor_chain",
        r#"
using System;
using System.Reflection;
class Base { ~Base() { Console.WriteLine("~Base"); } }
class Derived : Base { ~Derived() { Console.WriteLine("~Derived"); throw new Exception("boom"); } }
class G<T> { ~G() { Console.WriteLine("~G " + typeof(T).Name); } }
class H : G<int> { ~H() => Console.WriteLine("~H"); }
static class P
{
    static void Finalize(object o)
    {
        try { o.GetType().GetMethod("Finalize", BindingFlags.NonPublic | BindingFlags.Instance).Invoke(o, null); }
        catch (TargetInvocationException e) { Console.WriteLine(e.InnerException.Message); }
        GC.SuppressFinalize(o);
    }
    static void Main()
    {
        Finalize(new Derived());
        Finalize(new H());
    }
}
"#,
        "~Derived\n~Base\nboom\n~H\n~G Int32\n",
    );
}

#[test]
fn a_closure_class_inside_a_generic_local_function_declares_its_parameters() {
    check(
        "generic_local_function_closures",
        r#"
using System;
using System.Collections.Generic;
class C<T0>
{
    public void M<T1>(T1 t1, T0 t0)
    {
        int k = 5;
        void L1<T2>(T2 t2)
        {
            string L2<T3>(T3 t3, int n) => n == 0 ? $"{k} {t0} {t1} {t2} {t3} {typeof(T2).Name}" : L2(t3, n - 1);
            Console.WriteLine(L2(1.5, 2));
            Func<char, int, string> g = L2;
            Console.WriteLine(g('x', 1));
            Func<string> f = () => $"{t2}{k}";
            Console.WriteLine(f());
        }
        L1("s");
        L1(2);
        var fs = new List<Func<string>>();
        foreach (var x in new[] { 1, 2 }) { T1 y = t1; fs.Add(() => $"{x}{y}{t0}{k}"); }
        foreach (var f in fs) Console.WriteLine(f());
    }
}
static class P
{
    static void Main() => new C<string>().M<long>(7, "a");
}
"#,
        "5 a 7 s 1.5 String\n5 a 7 s x String\ns5\n5 a 7 2 1.5 Int32\n5 a 7 2 x Int32\n25\n17a5\n27a5\n",
    );
}

#[test]
fn a_conditional_access_nothing_reads_needs_no_nullable() {
    check(
        "conditional_access_unread",
        r#"
using System;
class C<T>
{
    public T M() { Console.WriteLine("M"); return default; }
    public R N() { Console.WriteLine("N"); return default; }
    public ref struct R { }
    static void M1(Action<C<T>> x, C<T> y) { Console.WriteLine("Action"); x(y); }
    static void M1(Func<C<T>, object> x, C<T> y) { Console.WriteLine("Func"); x(y); }
    public static void Test()
    {
        M1(a => a?.M(), new C<T>());
        C<T> c = new C<T>();
        c?.N();
        c = null;
        c?.N();
        c?.M();
    }
}
static class P
{
    static void Main() => C<int>.Test();
}
"#,
        "Action\nM\nN\n",
    );
}

#[test]
fn an_inaccessible_or_uninvocable_member_hides_nothing() {
    check(
        "hiding_by_kind_and_access",
        r#"
using System;
class Base<T>
{
    public virtual T P { get { Console.WriteLine("Base.get_P"); return default; } set { } }
    public virtual void M() { Console.WriteLine("Base.M"); }
}
class Middle<T> : Base<T>
{
    private new T P { set { } }
    public new delegate void M();
}
class Derived : Middle<int>
{
    public override int P { get { return base.P; } }
    static void Main()
    {
        var d = new Derived();
        Console.WriteLine(d.P);
        d.M();
    }
}
abstract class B<T> { public abstract T Method(int x); }
abstract class B2<A> : B<A> { public override A Method(int x) => default; public abstract A Method(A x); }
"#,
        "Base.get_P\n0\nBase.M\n",
    );
}

#[test]
fn an_overload_in_a_generic_derived_class_puts_out_its_base_s() {
    check(
        "overloads_through_generic_bases",
        r#"
using System;
abstract class Base<T> { public abstract T Method(int x); }
abstract class Base2<A> : Base<A> { public override A Method(int x) => default; public abstract A Method(A x); }
class Derived : Base2<long>
{
    public override long Method(int x) => 1;
    public override long Method(long x) => 2;
    static void Main()
    {
        Base2<long> b = new Derived();
        int i = 1;
        Console.WriteLine(b.Method(i));
    }
}
"#,
        "2\n",
    );
}

#[test]
fn closures_are_named_and_shared_the_way_roslyn_does() {
    check(
        "closure_names",
        r#"
using System;
using System.Linq;
using System.Reflection;
class C<T>
{
    int f = 1;
    int P { get; set; }
    event Action E;
    public void M(int k, params int[] rest)
    {
        Func<int, int> a = x => x + 1;
        int L(int y) => y + k;
        Func<int> b = () => L(1);
        Func<int> c = () => 2;
        Func<int> d = () => 2;
        Console.WriteLine(a(1) + b() + c() + d() + " " + (Make() == Make()) + " " + c.Target.GetType().IsSerializable);
        var lam = (params int[] xs) => xs.Length;
        Console.WriteLine(lam(1, 2));
    }
    static Func<int> Make() => () => 5;
    static void Main() { }
}
static class P
{
    static void Main()
    {
        new C<string>().M(1);
        var all = typeof(C<>).GetNestedTypes(BindingFlags.NonPublic).Prepend(typeof(C<>))
            .SelectMany(t => t.GetMethods(BindingFlags.Instance | BindingFlags.Static | BindingFlags.NonPublic | BindingFlags.DeclaredOnly)
                .Where(m => m.Name.Contains("__"))
                .Select(m => t.Name + " " + m.Name + " " + string.Join(",", m.GetParameters().SelectMany(p => p.CustomAttributes).Select(a => a.AttributeType.Name))))
            .OrderBy(n => n, StringComparer.Ordinal);
        foreach (var name in all) Console.WriteLine(name);
    }
}
"#,
        "8 True True\n2\n<>c <M>b__8_0 \n<>c <M>b__8_3 \n<>c <M>b__8_4 \n<>c <M>b__8_5 ParamArrayAttribute\n<>c <Make>b__9_0 \n<>c__DisplayClass8_0 <M>b__2 \n<>c__DisplayClass8_0 <M>g__L|1 \n",
    );
}

#[test]
fn foreach_reaches_extension_enumerators_by_reference_and_over_tuples() {
    check(
        "foreach_extension_enumerators",
        r#"
using System;
using System.Collections.Generic;
public struct S
{
    public struct Enumerator
    {
        public int Current { get; private set; }
        public bool MoveNext() => Current++ != 3;
    }
}
public class R { }
public static class Extensions
{
    public static S.Enumerator GetEnumerator(this in S self) => new S.Enumerator();
    public static S.Enumerator Shared = new S.Enumerator();
    public static ref S.Enumerator GetEnumerator(this R self) => ref Shared;
    public static IEnumerator<T> GetEnumerator<T>(this (T first, T second) self)
    {
        yield return self.first;
        yield return self.second;
    }
}
static class P
{
    static void Main()
    {
        var s = new S();
        foreach (var i in s) Console.Write(i);
        foreach (var i in new S()) Console.Write(i);
        foreach (var i in new R()) Console.Write(i);
        foreach (var i in new R()) Console.Write(i);
        foreach (var i in (7, 8)) Console.Write(i);
        Console.WriteLine();
    }
}
"#,
        "12312312312378\n",
    );
}

#[test]
fn a_readonly_reference_to_a_covariant_array_element_is_not_type_checked() {
    check(
        "readonly_covariant_element",
        r#"
using System;
static class P
{
    static void Main()
    {
        object[] objects = new string[] { "hi", "there" };
        Test(objects[0]);
        Test(in objects[1]);
        Test(Element(objects));
        Console.WriteLine();
    }
    static ref readonly T Element<T>(T[] array)
    {
        Test(in array[0]);
        return ref array[1];
    }
    static void Test<T>(in T value) => Console.Write(value);
}
"#,
        "hitherehithere\n",
    );
}

#[test]
fn return_attributes_go_on_the_return_parameter() {
    check(
        "return_attributes",
        r#"
using System;
class A : Attribute { public A(string s) { S = s; } public string S; public override string ToString() => "A " + S; }
partial class C
{
    [return: A("one")]
    string Goo() => "";
    [return: A("two")]
    partial void Bar() { }
    partial void Bar();
    [A("method")]
    void Baz() { }
    static void Main()
    {
        var c = new C();
        Console.WriteLine(((Func<string>)c.Goo).Method.ReturnTypeCustomAttributes.GetCustomAttributes(false)[0]);
        Console.WriteLine(((Action)c.Bar).Method.ReturnTypeCustomAttributes.GetCustomAttributes(false)[0]);
        Console.WriteLine(((Action)c.Baz).Method.ReturnTypeCustomAttributes.GetCustomAttributes(false).Length);
    }
}
"#,
        "A one\nA two\n0\n",
    );
}

#[test]
fn an_explicit_implementation_names_its_interface_in_the_type_s_terms() {
    check(
        "explicit_in_type_terms",
        r#"
using System;
using System.Collections.Generic;
class Outer<T>
{
    internal class Inner<U>
    {
        internal interface I<V> { T P { set; } void M<W>(List<W> c, V v); }
        internal class D1 : Inner<int>.I<long>
        {
            T Outer<T>.Inner<int>.I<long>.P { set { Console.WriteLine("D1.P " + typeof(T).Name); } }
            void Inner<int>.I<long>.M<W>(List<W> c, long v) { Console.WriteLine("D1.M"); }
        }
    }
}
interface J<V> { void M<W>(List<W> c); }
class D<X> : J<X> { void J<X>.M<X>(List<X> c) { Console.WriteLine("D.M " + typeof(X).Name); } }
static class P
{
    static void Main()
    {
        Outer<string>.Inner<int>.I<long> x = new Outer<string>.Inner<byte>.D1();
        x.P = "";
        x.M<int>(null, 1);
        J<int> j = new D<int>();
        j.M<string>(null);
    }
}
"#,
        "D1.P String\nD1.M\nD.M String\n",
    );
}

#[test]
fn a_deconstruction_is_worth_the_tuple_of_what_it_assigned() {
    check(
        "deconstruction_value",
        r#"
using System;
class P
{
    public void Deconstruct(out int a, out int b) { a = 7; b = 8; }
}
class C
{
    int _test1;
    int this[int x] { get => _test1; set { Console.Write("[set " + value + "]"); _test1 = value; } }
    static void Main()
    {
        int x; long y;
        var a = (x, _) = (2, 123);
        Console.WriteLine(a);
        var c = ((x, _), y) = ((5, "s"), 6);
        Console.WriteLine(c + " " + x + " " + y);
        Console.WriteLine((x, y) = new P());
        dynamic d = 1;
        var o = new C();
        var t = (o[d], _) = (2, 123);
        Console.WriteLine(t + " " + o._test1);
        (x, _) = (9, 10);
        for ((x, y) = (0, 0); x < 2; (x, y) = (x + 1, y + 2)) Console.Write(y);
        Console.WriteLine();
    }
}
"#,
        "(2, 123)\n((5, s), 6) 5 6\n(7, 8)\n[set 2](2, 123) 2\n02\n",
    );
}

#[test]
fn a_spread_into_a_collection_filled_through_add_is_walked_where_it_stands() {
    check(
        "spread_through_add",
        r#"
using System;
using System.Collections;
using System.Collections.Generic;
using System.Threading.Tasks;
class MyC : IEnumerable<int>
{
    List<int> l = new();
    public void Add(int x) { Console.Write("+" + x); l.Add(x); }
    public IEnumerator<int> GetEnumerator() => l.GetEnumerator();
    IEnumerator IEnumerable.GetEnumerator() => l.GetEnumerator();
    public override string ToString() => "[" + string.Join(",", l) + "]";
}
struct Bag<T> : IEnumerable
{
    private List<T> _list = new();
    public Bag() { }
    internal void AddValue(T t) { _list.Add(t); }
    public IEnumerator<T> GetEnumerator() => _list.GetEnumerator();
    IEnumerator IEnumerable.GetEnumerator() => _list.GetEnumerator();
}
static class Extensions
{
    public static void Add<T>(this ref Bag<T> c, in T t) { c.AddValue(t); }
    public static void Add<T>(this ICollection<T> collection, params T[] elements)
    {
        foreach (T element in elements) collection.Add(element);
    }
}
class P
{
    static int A(int x) { Console.Write("A" + x); return x; }
    static IEnumerable<int> E() { Console.Write("E"); yield return 7; yield return 8; }
    static void M(int a, MyC c, int b) { Console.WriteLine(" M " + a + c + b); }
    static IEnumerable<MyC> It() { yield return [A(1), ..E()]; }
    static async Task<MyC> As() { await Task.Yield(); MyC c = [..E(), A(await Task.FromResult(3))]; return c; }
    static void Main()
    {
        M(A(0), [A(1), ..E(), A(2)], A(3));
        Func<MyC> f = () => [..E(), ..new[] { 5, 6 }];
        Console.WriteLine(f());
        foreach (var c in It()) Console.WriteLine(c);
        Console.WriteLine(As().Result);
        Span<int> sp = stackalloc int[] { 4, 4 };
        MyC y = [..sp];
        Console.WriteLine(y);
        dynamic d = new List<int> { 1 };
        MyC z = [..d];
        Console.WriteLine(z);
        Bag<object> x = new() { 1 };
        Bag<int> e = [];
        Bag<object> b = [..x, ..e, 3];
        foreach (var i in b) Console.Write(i + ";");
        Console.WriteLine();
        var pairs = new KeyValuePair<string, string>[] { new("a", "b") };
        Dictionary<string, string> map = [..pairs];
        Console.WriteLine(map["a"]);
    }
}
"#,
        "A0A1+1E+7+8A2+2A3 M 0[1,7,8,2]3\nE+7+8+5+6[7,8,5,6]\nA1+1E+7+8[1,7,8]\nE+7+8A3+3[7,8,3]\n+4+4[4,4]\n+1[1]\n1;3;\nb\n",
    );
}

#[test]
fn a_const_decimal_is_a_static_readonly_field_that_says_its_value() {
    check(
        "decimal_constant",
        r#"
using System;
using System.Reflection;
public class C
{
    public const decimal A = 10000.213213M;
    public const decimal B = -A;
    public const decimal Max = decimal.MaxValue;
    public const decimal Seven = 7;
    public static readonly decimal NotConstant = 1.5m;
    static void Main()
    {
        foreach (var field in typeof(C).GetFields())
        {
            Console.Write(field.Name + " " + field.IsInitOnly + " " + field.GetValue(null));
            foreach (var data in field.GetCustomAttributesData())
            {
                Console.Write(" [");
                foreach (var argument in data.ConstructorArguments) Console.Write(argument.Value + ";");
                Console.Write("]");
            }
            Console.WriteLine();
        }
    }
}
"#,
        "A True 10000.213213 [6;0;0;2;1410278621;]\nB True -10000.213213 [6;128;0;2;1410278621;]\nMax True 79228162514264337593543950335 [0;0;4294967295;4294967295;4294967295;]\nSeven True 7 [0;0;0;0;7;]\nNotConstant True 1.5\n",
    );
}

#[test]
fn a_utf8_literal_is_made_through_the_spans_array_start_and_length_constructor() {
    check(
        "utf8_user_span",
        r#"
public class C
{
    static void Main()
    {
        System.ReadOnlySpan<byte> s = "ab"u8;
        System.Console.WriteLine(s.Length + " " + s.Count + " " + s[1]);
    }
}
namespace System
{
    public readonly ref struct ReadOnlySpan<T>
    {
        private readonly T[] arr;
        public ref readonly T this[int i] => ref arr[i];
        public int Length { get; }
        public int Count { get; }
        public ReadOnlySpan(T[] arr, int start, int length)
        {
            this.arr = arr;
            this.Length = arr.Length;
            this.Count = length;
        }
    }
}
"#,
        "3 2 98\n",
    );
}

#[test]
fn a_collection_expression_takes_with_arguments_and_infers_its_element_type() {
    check(
        "collection_with_arguments",
        r#"
using System;
using System.Collections;
using System.Collections.Generic;
using System.Runtime.CompilerServices;
class MyList<T> : List<T>
{
    public MyList(out int value, string name = "x") : base() { value = 42; Console.Write(name + ";"); }
}
[CollectionBuilder(typeof(Builder), nameof(Builder.Create))]
struct Bag<T> : IEnumerable<T>
{
    public List<T> Items;
    public IEnumerator<T> GetEnumerator() => Items.GetEnumerator();
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}
static class Builder
{
    public static Bag<T> Create<T>(int extra, ReadOnlySpan<T> items)
    {
        var list = new List<T>(items.ToArray());
        Console.Write("extra " + extra + ";");
        return new Bag<T> { Items = list };
    }
}
class Static : IEnumerable
{
    public List<object> Items = new();
    public static void Add(object o) => throw null;
    public IEnumerator GetEnumerator() => Items.GetEnumerator();
}
static class E
{
    public static void Add(this Static s, object o) => s.Items.Add(o);
    public static void Report(this object o) => Console.WriteLine("object");
    public static void Report<T>(this in ReadOnlySpan<T> s) => Console.WriteLine("span " + s.Length);
}
class P
{
    static List<T> ListOf<T>(int capacity) => [with(capacity: capacity)];
    static T[] First<T>(T[][] x) => x[0];
    static IEnumerable<T> Same<T>(IEnumerable<T> items) => items;
    static void Main()
    {
        MyList<int> list = [with(out var x, name: "n"), x, x + 1];
        Console.WriteLine(list.Count + " " + list[1] + " " + x);
        Console.WriteLine(ListOf<int>(16).Capacity);
        Bag<int> bag = [with(7), 1, 2];
        Console.WriteLine(bag.Items.Count);
        IList<int> mutable = [1, 2];
        mutable.Add(3);
        Console.WriteLine(mutable.GetType().Name + " " + mutable.Count);
        int[] ints = [4, 5];
        object[] boxed = [..ints, "s"];
        Console.WriteLine(boxed.Length + " " + boxed[2]);
        Console.WriteLine(First([[1, 2, 3]]).Length);
        foreach (var item in Same([..ints, 6])) Console.Write(item);
        Console.WriteLine();
        Static s = [1, ..ints];
        Console.WriteLine(s.Items.Count);
        Span<int> span = ints;
        span.Report();
    }
}
"#,
        "n;2 43 42\n16\nextra 7;2\nList`1 3\n3 s\n3\n456\n3\nspan 2\n",
    );
}

#[test]
fn before_csharp_10_a_lambda_has_no_type_of_its_own() {
    // Roslyn's DelegateTypeTests.OverloadResolution_08: `F(Delegate)` takes
    // a lambda through its natural type only from C# 10 on; before, the
    // extension method taking a `Func` is the one that applies.
    let source = r#"
using System;
using static System.Console;
class C
{
    static void Main()
    {
        var c = new C();
        c.F(x => x);
        c.F((int x) => x);
    }
    void F(Delegate d) => Write("instance, ");
}
static class Extensions
{
    public static void F(this C c, Func<int, int> f) => Write("extension, ");
}
"#;
    use rustlyn_syntax::LanguageVersion;
    let options = rustlyn_semantics::CompilationOptions::default();
    check_with_options(
        "LambdaNaturalType9",
        LanguageVersion::CSharp9,
        options.clone(),
        source,
        "extension, extension, ",
    );
    check_with_options(
        "LambdaNaturalType10",
        LanguageVersion::CSharp10,
        options,
        source,
        "extension, instance, ",
    );
}

#[test]
fn before_csharp_10_a_generic_parameter_infers_nothing_from_a_lambda() {
    // OverloadResolution_26 and _45: `F<T>(T)` is not applicable to a
    // lambda that has no type, and neither is an indexer taking `Delegate`,
    // so `F(Action)` and the base class's indexer are. (From C# 10 on the
    // indexer taking `Delegate` applies and, being the derived class's,
    // hides the base's.)
    let source = r#"
using System;
class A
{
    public object this[Func<int> f] => Report("A");
    public static object Report(string message) { Console.Write(message); return null; }
}
class B : A
{
    public object this[Delegate d] => Report("B");
}
class Program
{
    static void F(Action action) => Console.Write("Action ");
    static void F<T>(T t) => Console.Write(typeof(T).Name + " ");
    static void Main()
    {
        int i = 0;
        F(() => i++);
        _ = new B()[() => 1];
    }
}
"#;
    use rustlyn_syntax::LanguageVersion;
    let options = rustlyn_semantics::CompilationOptions::default();
    check_with_options(
        "LambdaInference9",
        LanguageVersion::CSharp9,
        options.clone(),
        source,
        "Action A",
    );
    let indexer = source.replace("int i = 0;\n        F(() => i++);", "");
    check_with_options(
        "LambdaInference10",
        LanguageVersion::CSharp10,
        options,
        &indexer,
        "B",
    );
}

#[test]
fn before_csharp_12_a_ref_argument_does_not_reach_an_in_parameter() {
    // RefReadonlyParameterTests.OverloadResolution_ExtensionMethod_01.
    let source = r#"
class C
{
    string M1(in int i) => "C";
    static void Main()
    {
        int i = 5;
        System.Console.Write(new C().M1(ref i));
        System.Console.Write(new C().M1(in i));
        System.Console.Write(new C().M1(i));
    }
}
static class E
{
    public static string M1(this C c, ref int i) => "E";
}
"#;
    use rustlyn_syntax::LanguageVersion;
    let options = rustlyn_semantics::CompilationOptions::default();
    check_with_options(
        "RefToIn11",
        LanguageVersion::CSharp11,
        options.clone(),
        source,
        "ECC",
    );
    check_with_options(
        "RefToIn12",
        LanguageVersion::CSharp12,
        options,
        source,
        "CCC",
    );
}

#[test]
fn main_names_the_type_whose_main_starts_the_program() {
    let source = r#"
class A { static void Main() => System.Console.Write("A"); }
namespace N { class B { static void Main() => System.Console.Write("B"); } }
"#;
    let options = rustlyn_semantics::CompilationOptions {
        main_type_name: Some("N.B".to_string()),
        ..Default::default()
    };
    check_with_options(
        "ExplicitMain",
        rustlyn_syntax::LanguageVersion::default(),
        options,
        source,
        "B",
    );
}

#[test]
fn checked_makes_arithmetic_outside_any_region_checked() {
    let source = r#"
class P
{
    static void Main()
    {
        int x = int.MaxValue;
        try { x = x + 1; System.Console.Write("wrapped "); }
        catch (System.OverflowException) { System.Console.Write("overflow "); }
        unchecked { x = x + 1; }
        System.Console.Write(x);
    }
}
"#;
    let options = rustlyn_semantics::CompilationOptions {
        check_overflow: true,
        ..Default::default()
    };
    check_with_options(
        "CheckedOption",
        rustlyn_syntax::LanguageVersion::default(),
        options,
        source,
        "overflow -2147483648",
    );
}

#[test]
fn a_file_local_type_is_its_own_in_each_file_and_named_after_it() {
    // FileModifierTests: `file class C` in two files are two types, each
    // seen only in its file, and metadata names each after the file's name
    // and the SHA-256 of its path.
    let Some(bytes) = references() else {
        println!("note: file-local types were skipped; no .NET shared framework was found");
        return;
    };
    let first = r#"
file class C { public static string M() => "one "; }
class Program
{
    static void Main()
    {
        System.Console.Write(C.M());
        System.Console.Write(Other.M());
        System.Console.Write(typeof(C).Name);
    }
}
"#;
    let second = r#"
file class C { public static string M() => "two "; }
class Other { public static string M() => C.M(); }
"#;
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
    let compilation = Compilation::create_with_references(
        vec![
            parse(SourceText::new("", first)),
            parse(SourceText::new("dir/file2.cs", second)),
        ],
        &images,
    );
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    let name = "FileLocalTypes";
    let emitted = rustlyn_emit::emit(&compilation, name).expect("the program should emit");
    run_emitted(
        name,
        &scratch(name),
        &emitted,
        "one two <>FE3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855__C",
    );
}

#[test]
fn field_is_the_backing_field_from_csharp_14_and_an_ordinary_name_before() {
    // FieldKeywordTests: before C# 14 `field` in an accessor names the member
    // called `field`; from C# 14 on it is the property's own backing field,
    // and the member is `@field`.
    let source = r#"
using System;
class C
{
    int field = 7;
    public int P { get { return field; } set { field = value; } }
    public int Q { get { return @field + 1; } }
    // An indexer has no backing field: `field` is the member here.
    public int this[int i] => field + i;
}
class Program
{
    static void Main()
    {
        var c = new C();
        c.P = 3;
        Console.Write((c.P, c.Q, c[10]));
    }
}
"#;
    use rustlyn_syntax::LanguageVersion;
    let options = rustlyn_semantics::CompilationOptions::default();
    check_with_options(
        "FieldKeyword13",
        LanguageVersion::CSharp13,
        options.clone(),
        source,
        "(3, 4, 13)",
    );
    check_with_options(
        "FieldKeyword14",
        LanguageVersion::CSharp14,
        options,
        source,
        "(3, 8, 17)",
    );
}

#[test]
fn a_lambda_returning_a_lambda_gives_way_before_csharp_10() {
    // OverloadResolutionTests.ExactlyMatchingNestedLambda: before C# 10 the
    // inner lambda has no type, so the outer one has no inferred return
    // type, and what it says about `DA` over `DB` gives way to the `int`
    // argument's exact match (Roslyn's bug 11961 deviation).
    let source = r#"
using System;
class P
{
  delegate Func<int> DA();
  delegate Func<object> DB();

  static void M1(DA a, object b) { Console.Write(1); }
  static void M1(DB a, int b) { Console.Write(2); }

  static void Main()
  {
    int i = 0;
    M1(() => () => i, i);
  }
}
"#;
    check_with_options(
        "NestedLambdaGivesWay9",
        rustlyn_syntax::LanguageVersion::CSharp9,
        rustlyn_semantics::CompilationOptions::default(),
        source,
        "2",
    );
}

#[test]
fn spans_are_first_class_from_csharp_14() {
    // FirstClassSpanTests: from C# 14 an array converts to a span by a
    // conversion of the language's own, which beats any other, a
    // `ReadOnlySpan<T>` is the better target than a `Span<T>`, `T` is
    // inferred from an array's element, extension receivers take the
    // conversion, and arrays, spans and strings reach a `ReadOnlySpan` of a
    // base type covariantly.
    let source = r#"
using System;
using System.Collections.Generic;
static class E
{
    static void A(this ReadOnlySpan<int> s) => Console.Write("receiver ");
    static void A(this IEnumerable<int> s) => Console.Write("enumerable ");
    static void C(ReadOnlySpan<int> s) => Console.Write("ROS ");
    static void C(Span<int> s) => Console.Write("Span ");
    static void D(IEnumerable<int> s) => Console.Write("IEnumerable ");
    static void D(Span<int> s) => Console.Write("Span ");
    static void Main()
    {
        int[] a = { 1, 2 };
        a.A();
        C(a);
        D(a);
#if SPANS
        Console.Write(Sum(a));
        string[] strings = { "x", "y" };
        ReadOnlySpan<object> objects = strings;
        Span<string> span = strings;
        ReadOnlySpan<object> up = span;
        ReadOnlySpan<char> chars = "hi";
        Console.Write($" {objects[1]}{up.Length}{chars[1]}");
#endif
    }
    static int Sum<T>(Span<T> s) => s.Length;
}
"#;
    use rustlyn_syntax::LanguageVersion;
    let options = rustlyn_semantics::CompilationOptions::default();
    check_with_options(
        "FirstClassSpans13",
        LanguageVersion::CSharp13,
        options.clone(),
        source,
        "enumerable Span IEnumerable ",
    );
    check_with_options(
        "FirstClassSpans14",
        LanguageVersion::CSharp14,
        options,
        &source.replace("#if SPANS", "#if true"),
        "receiver ROS Span 2 y2i",
    );
}

#[test]
fn overload_resolution_priority_counts_from_csharp_13() {
    // OverloadResolutionPriorityTests: from C# 13 on, only the applicable
    // members of the highest priority a type declares stay candidates; a
    // `long` constant reaches `ulong` alone, so `M1(uint)` never applies.
    let source = r#"
using System.Runtime.CompilerServices;
class Program
{
    static void Main()
    {
        M(1);
        M1(0L);
    }
    static void M(int x) => System.Console.Write("int ");
    [OverloadResolutionPriority(1)]
    static void M(long x) => System.Console.Write("long ");
    static void M1(int x) => System.Console.Write(1);
    [OverloadResolutionPriority(1)]
    static void M1(uint x) => System.Console.Write(2);
    static void M1(long x) => System.Console.Write(3);
}
"#;
    use rustlyn_syntax::LanguageVersion;
    let options = rustlyn_semantics::CompilationOptions::default();
    check_with_options(
        "Priority12",
        LanguageVersion::CSharp12,
        options.clone(),
        source,
        "int 3",
    );
    check_with_options(
        "Priority13",
        LanguageVersion::CSharp13,
        options,
        source,
        "long 3",
    );
}

#[test]
fn partial_constructors_and_events_are_one_member_each() {
    // PartialEventsAndConstructorsTests (C# 14): the part with the body or
    // the accessors is the member; the declaring part adds no field-like
    // event and no second constructor.
    check(
        "PartialEventsAndConstructors",
        r#"
using System;

var c = new C();
c.E += () => Console.Write(1);
c.E -= () => Console.Write(2);

partial class C
{
    public partial event Action E;
    public partial event Action E
    {
        add { Console.Write(3); value(); }
        remove { Console.Write(4); value(); }
    }
    public partial C();
    public partial C() { Console.Write(5); }
}
"#,
        "53142",
    );
}

/// As [`check`], with the source parsed as `version` of C# and compiled with
/// `options`: what `/langversion:`, `/main:` and `/checked` change.
#[track_caller]
fn check_with_options(
    name: &str,
    version: rustlyn_syntax::LanguageVersion,
    options: rustlyn_semantics::CompilationOptions,
    source: &str,
    expected: &str,
) {
    let Some(bytes) = references() else {
        println!("note: {name} was skipped; no .NET shared framework was found");
        return;
    };
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
    let parse_options = rustlyn_syntax::ParseOptions::default().with_language_version(version);
    let compilation = Compilation::create_with_references(
        vec![rustlyn_syntax::parse_with(
            SourceText::new("Program.cs", source),
            &parse_options,
        )],
        &images,
    )
    .with_options(options);
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        // A warning (`string?` outside a `#nullable` context) is not a
        // failure to compile.
        .filter(|entry| entry.diagnostic.is_error())
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(
        diagnostics.is_empty(),
        "{name} did not compile: {diagnostics:#?}"
    );
    let emitted = rustlyn_emit::emit(&compilation, name)
        .unwrap_or_else(|error| panic!("{name} could not be emitted: {error}"));
    run_emitted(name, &scratch(name), &emitted, expected);
}

#[test]
fn type_inference_fixes_bounds_through_lambdas_and_tuples() {
    check(
        "type_inference_phases",
        r#"
using System;
using System.Collections.Generic;
static class P
{
    static void Tuple3<T>((Func<int, T>, Func<T, T>) x) => Console.Write("third " + x.Item1(5) + " ");
    static void Tuple3<T>((T, T) x) => Console.Write("first ");
    static void Pair<U>(Func<int, (U, U)> f1, Func<(U, U), int> f2) => Console.Write(f2(f1(1)) + " ");
    static void Named<U, T>(U f1, Func<U, (T x, T y)> f2) => Console.Write(f2(f1).y + " ");
    static void Same<T>(T x, T y, Func<T, int> f) => Console.Write("same ");
    static void Same<T>(T x, object y, Func<T, int> f) => Console.Write("object ");
    static void Assert<T>(T a, T b) => Console.Write("single ");
    static void Assert<T>(IEnumerable<T> a, IEnumerable<T> b) => Console.Write("collection ");
    static void Nested(Func<Func<short>> x) => Console.Write("short ");
    static void Nested(Func<Func<int>> x) => Console.Write("int ");
    class Values : List<string>
    {
        public static implicit operator Values(string[] values) => new Values();
        public static implicit operator string[](Values value) => new string[0];
    }
    static void Main()
    {
        Tuple3(((x) => x, (x) => x));
        Pair((x) => (x, x), (t) => 1);
        Named((a: 1, b: 2), (t) => (t.a, t.b));
        Same((a: 1, b: 2), (c: 3, d: 4), t => t.a);
        Assert(new[] { "A" }, new Values());
        bool val = false;
        Nested(() => { if (val) return () => 0; else return () => 0; });
        nuint u = 5;
        Console.Write(u > 0);
    }
}
"#,
        "third 5 1 2 object collection int True",
    );
}

#[test]
fn queries_join_and_reach_custom_query_methods() {
    check(
        "query_join_and_custom",
        r#"
using System;
using System.Linq;
class Y
{
    public int Where(Func<int, bool> predicate) => predicate(1) ? 45 : 0;
}
static class P
{
    static void Main()
    {
        var a = new[] { 1, 2, 3, 4 };
        var b = new[] { 2, 4, 6, 8 };
        Console.WriteLine(string.Join(" ", from x in a join y in b on x * 2 equals y select x + y));
        Console.WriteLine(string.Join(" ", from x in a join y in b on x * 2 equals y where x > 1 select x * 100 + y));
        Console.WriteLine(string.Join(" ", from x in a join y in b on x equals y into g select x + ":" + g.Count()));
        Console.WriteLine(string.Join(" ", from x in a where x > 2 select x));
        Console.WriteLine(from x in new Y() where x > 0 select x);
    }
}
"#,
        "3 6 9 12\n204 306 408\n1:0 2:1 3:0 4:1\n3 4\n45\n",
    );
}

#[test]
fn named_in_arguments_keep_the_references_they_were_given() {
    check(
        "named_in_references",
        r#"
using System;
readonly struct S
{
    public readonly int x;
    public S(int x) { this.x = x; }
    static S[] arr = new S[] { new S() };
    static ref S I(int arg) { arr[0] = new S(arg); return ref arr[0]; }
    static ref readonly S RO(in S arg1, in S arg2) { Console.Write(arg2.x); return ref arg2; }
    static void Main()
    {
        Console.WriteLine(RO(arg2: I(5), arg1: I(3)).x);
        var d = new D();
        Console.WriteLine(d[0] ??= "set");
    }
}
class D
{
    object field = null;
    public ref object this[int i] => ref field;
}
"#,
        "33\nset\n",
    );
}

#[test]
fn a_candidate_inferring_an_inaccessible_type_is_not_applicable() {
    check(
        "inaccessible_inferred_type",
        r#"
using System;
interface J<T> { }
interface I<T> : J<object> { }
class A
{
    private class B { }
    public class C : I<B> { }
}
static class P
{
    static void Main() => Goo(new A.C());
    static void Goo<T>(I<T> x) => Console.WriteLine("I");
    static void Goo<T>(J<T> x) => Console.WriteLine("J " + typeof(T).Name);
}
"#,
        "J Object\n",
    );
}

#[test]
fn a_multidimensional_array_is_walked_by_nested_loops() {
    check(
        "multidimensional_foreach",
        r#"
using System;
using System.Collections.Generic;
using System.Threading.Tasks;
unsafe static class P
{
    static IEnumerable<int> It(int[,] a) { foreach (var x in a) { if (x == 5) continue; yield return x; } }
    static async Task Main()
    {
        var a = new int[2, 3] { { 1, 2, 3 }, { 4, 5, 6 } };
        foreach (var x in a) { if (x == 2) continue; if (x == 6) break; Console.Write(x); }
        Console.WriteLine();
        var b = (int[,,])Array.CreateInstance(typeof(int), new[] { 2, 2, 2 }, new[] { 1, -1, 5 });
        int k = 0;
        for (int i = 1; i <= 2; i++) for (int j = -1; j <= 0; j++) for (int l = 5; l <= 6; l++) b[i, j, l] = k++;
        foreach (var x in b) Console.Write(x);
        Console.WriteLine();
        foreach (var x in It(a)) Console.Write(x);
        Console.WriteLine();
        int*[,] pointers = new [,] { { (int*)1, (int*)2 }, { (int*)3, (int*)4 } };
        foreach (var p in pointers) Console.Write((int)p);
        foreach (var x in new int[2, 1] { { 7 }, { 8 } }) { await Task.Yield(); Console.Write(x); }
        foreach (var s in new string[0, 3]) Console.Write("never");
        Console.WriteLine();
    }
}
"#,
        "1345\n01234567\n12346\n123478\n",
    );
}

#[test]
fn an_argument_without_in_prefers_a_value_parameter() {
    check(
        "in_versus_value_overloads",
        r#"
using System;
class P
{
    static void M(in int x, int a = 0) => Console.Write("in" + x + " ");
    static void M(int x, int a = 0, int b = 0) => Console.Write("val" + x + " ");
    int this[in int inP] { get { Console.Write("in" + inP + " "); return 0; } }
    int this[int valP] { get { Console.Write("val" + valP + " "); return 0; } }
    static void Main()
    {
        int x = 1;
        M(x); M(in x); M(2, 0);
        var p = new P();
        _ = p[3]; _ = p[in x]; _ = p[valP: 4]; _ = p[inP: 5];
        Console.WriteLine();
    }
}
"#,
        "val1 in1 val2 val3 in1 val4 in5 \n",
    );
}

#[test]
fn an_await_in_a_conditional_access_on_a_nullable_value_waits_for_the_test() {
    check(
        "await_in_nullable_conditional_access",
        r#"
using System;
using System.Threading.Tasks;
struct S { public int V; public int Add(int x) { Console.Write("add "); return V + x; } }
static class P
{
    static async Task<int> One() { await Task.Yield(); Console.Write("one "); return 1; }
    static async Task Main()
    {
        S? a = new S { V = 5 }; S? n = null;
        Console.WriteLine(a?.Add(await One()));
        Console.WriteLine(n?.Add(await One()) ?? -1);
        var arr = new S?[] { null, new S { V = 2 } };
        Console.WriteLine(arr[await One()]?.Add(await One()));
    }
}
"#,
        "one add 6\n-1\none one add 3\n",
    );
}

#[test]
fn a_lambda_s_attributes_go_on_its_method() {
    check(
        "lambda_attributes",
        r#"
using System;
using System.Linq;
class A : Attribute { public A(string s) { S = s; } public string S; public override string ToString() => "A(" + S + ")"; }
static class P
{
    static void Main()
    {
        Func<int, int> f = [A("m")] [return: A("r")] ([A("p")] x) => x;
        var m = f.Method;
        Console.WriteLine(string.Join(",", m.GetCustomAttributes(false).Select(a => a.ToString())));
        Console.WriteLine(string.Join(",", m.ReturnTypeCustomAttributes.GetCustomAttributes(false)));
        Console.WriteLine(string.Join(",", m.GetParameters()[0].GetCustomAttributes(false)));
        Action g = [Obsolete] () => { };
        Console.WriteLine(g.Method.GetCustomAttributes(false)[0]);
    }
}
"#,
        "A(m)\nA(r)\nA(p)\nSystem.ObsoleteAttribute\n",
    );
}

#[test]
fn a_main_type_names_where_the_program_starts() {
    let Some(bytes) = references() else {
        println!("note: main_type was skipped; no .NET shared framework was found");
        return;
    };
    let source = r#"
System.Console.WriteLine("statements");
class C { static void Main() => System.Console.WriteLine("C"); }
partial class Program { static void Main() => System.Console.WriteLine("Program"); }
namespace A.B { class D { static void Main() => System.Console.WriteLine("D"); } }
"#;
    for (main_type, expected) in [("C", "C\n"), ("Program", "Program\n"), ("A.B.D", "D\n")] {
        let name = format!("main_type_{}", main_type.replace('.', "_"));
        let compilation = compiled(&name, source, &bytes);
        let emitted = rustlyn_emit::emit_with_main_type(&compilation, &name, main_type)
            .unwrap_or_else(|error| panic!("{name} could not be emitted: {error}"));
        let directory = scratch(&name);
        run_emitted(&name, &directory, &emitted, expected);
    }
}

#[test]
fn a_library_with_its_own_in_attribute_is_called_with_that_one_in_its_signatures() {
    // The library's `D.Invoke` takes `modreq(its InAttribute) int&`, and the
    // program declares a third `InAttribute`: a reference naming either of
    // the others names a method the runtime does not have.
    check_with_library(
        "OwnInAttribute",
        r#"
namespace System.Runtime.InteropServices
{
    public class InAttribute {}
}
public delegate void D(in int p);
public delegate ref readonly int R();
"#,
        r#"
namespace System.Runtime.InteropServices
{
    public class InAttribute {}
}
public class Test
{
    private static int value = 5;
    public static void Main()
    {
        D d = (in int p) => System.Console.Write(p);
        d(value);
        R r = () => ref value;
        System.Console.WriteLine(r());
    }
}
"#,
        "55\n",
    );
}

#[test]
fn a_fixed_buffer_from_another_assembly_reads_as_a_pointer_to_its_elements() {
    check_with_library(
        "FixedBufferAcross",
        r#"
public unsafe struct S
{
    public fixed int x[10];
}
"#,
        r#"
using System;
class Program
{
    static void Main()
    {
        S s = default;
        unsafe
        {
            int* p = s.x;
            s.x[0] = 12;
            p[1] = p[0] + 1;
            Console.WriteLine(s.x[1]);
        }
    }
}
"#,
        "13\n",
    );
}

#[test]
fn function_pointers_take_addresses_and_call_through_them() {
    check(
        "FunctionPointers",
        r#"
using System;
unsafe class C
{
    static int field = 1;
    static int Twice(int x) => x * 2;
    static string Show(object o) => "<" + o + ">";
    static ref int Field() => ref field;
    static void M(delegate*<void> p) => Console.Write("void ");
    static void M(delegate*<object> p) => Console.Write(p() + " ");
    static void Write(string s) => Console.Write(s);
    static object Obj() => "object";
    static T Id<T>(T t) => t;
    static void Main()
    {
        delegate*<int, int> twice = &Twice;
        Console.Write(twice(21) + " ");
        // A method taking less than the pointer hands it fits, and so does
        // one returning more.
        delegate*<string, object> show = &Show;
        Console.Write(show("s") + " ");
        delegate*<ref int> r = &Field;
        r() = 7;
        Console.Write(field + " ");
        M(&Obj);
        delegate*<string, void>[] writers = new delegate*<string, void>[] { &Write, null };
        writers[0]("a ");
        Console.Write((writers[1] == null) + " ");
        delegate*<int, int> id = &Id<int>;
        Console.Write(id(3) + " ");
        // A pointer converts to one whose parameters are more derived.
        delegate*<object, string> general = &Show;
        delegate*<string, object> particular = general;
        Console.Write(particular("p") + " ");
        Console.WriteLine((void*)twice == (void*)twice);
    }
}
"#,
        "42 <s> 7 object a True 3 <p> True\n",
    );
}

#[test]
fn a_function_pointer_in_a_library_signature_is_read_back() {
    check_with_library(
        "FunctionPointerAcross",
        r#"
public unsafe static class Library
{
    public static int Add(int a, int b) => a + b;
    public static delegate*<int, int, int> Adder() => &Add;
    public static int Apply(delegate*<in int, int> f, int x) => f(x);
}
"#,
        r#"
using System;
unsafe class Program
{
    static int Square(in int x) => x * x;
    static void Main()
    {
        var add = Library.Adder();
        Console.WriteLine(add(2, 3) + Library.Apply(&Square, 4));
    }
}
"#,
        "21\n",
    );
}

#[test]
fn a_typed_reference_is_made_read_written_and_asked_its_type() {
    check(
        "TypedReferences",
        r#"
using System;
using System.Reflection;
class Holder { public int Value; }
class Program
{
    static void Main()
    {
        short x = 3;
        var r = __makeref(x);
        __refvalue(r, short) += 7;
        __refvalue(r, short)++;
        Console.Write(x + " " + __reftype(r).Name + " ");
        var holder = new Holder();
        typeof(Holder).GetField("Value").SetValueDirect(__makeref(holder), 34);
        Console.Write(holder.Value + " ");
        try
        {
            int wrong = __refvalue(r, int);
        }
        catch (InvalidCastException)
        {
            Console.WriteLine("cast");
        }
    }
}
"#,
        "11 Int16 34 cast\n",
    );
}

#[test]
fn in_arguments_and_ref_readonly_returns_read_covariant_array_elements_in_place() {
    // `object[]` that is really a `string[]`: `ldelema object` alone checks
    // the element type and throws, `readonly. ldelema` does not.
    check(
        "ReadonlyAddresses",
        r#"
class Program
{
    static void Main()
    {
        var objects = (object[])new string[] { "hi", "hello" };
        Test(objects[0]);
        Test(in objects[1]);
        Test(Element(objects));
    }
    static ref readonly T Element<T>(T[] array) => ref array[0];
    static void Test<T>(in T value) => System.Console.Write(value + " ");
}
"#,
        "hi hello hi ",
    );
}

#[test]
fn overloads_and_indexers_that_differ_only_by_in_prefer_the_one_the_call_site_wrote() {
    check(
        "InOverloads",
        r#"
using System;
class Program
{
    static void M(in int x, int op1 = 0) => Console.Write("in ");
    static void M(int x, int op1 = 0, int op2 = 0) => Console.Write("val ");
    static void N(int a, int b) => Console.Write("val ");
    static void N(in int b, int a) => Console.Write("in ");
    static void R(object o, in int i) => Console.Write("in ");
    static void R(string s, ref int i) => Console.Write("ref ");
    int this[in int i] { get { Console.Write("in "); return 0; } }
    int this[int v] { get { Console.Write("val "); return 0; } }
    static void Main()
    {
        int x = 1;
        M(x); M(in x); M(1);
        N(b: x, a: x); N(a: x, b: in x);
        R(null, ref x);
        var p = new Program();
        _ = p[0]; _ = p[in x]; _ = p[v: 2]; _ = p[i: 3];
        Console.WriteLine();
    }
}
"#,
        "val in val val in ref val in val in \n",
    );
}

#[test]
fn a_nested_initializer_reads_its_index_once() {
    check(
        "NestedInitializerIndex",
        r#"
using System.Collections.Generic;
class C
{
    public List<int>[] X = { new List<int>(), new List<int>() };
    static int Index { get { System.Console.Write("index "); return 1; } }
    static void Main()
    {
        var c = new C { X = { [Index] = { 1, 2 } } };
        System.Console.WriteLine(c.X[1].Count);
    }
}
"#,
        "index 2\n",
    );
}

#[test]
fn foreach_takes_an_in_or_ref_returning_get_enumerator_extension() {
    check(
        "ForEachThroughReferences",
        r#"
using System;
public struct S
{
    public struct Enumerator
    {
        public int Current { get; private set; }
        public bool MoveNext() => Current++ != 3;
    }
}
public class C { }
public static class Extensions
{
    public static S.Enumerator GetEnumerator(this in S self) => new S.Enumerator();
    public static S.Enumerator Instance = new S.Enumerator();
    public static ref S.Enumerator GetEnumerator(this C self) => ref Instance;
}
class Program
{
    static void Main()
    {
        foreach (var i in new S()) Console.Write(i);
        foreach (var i in new C()) Console.Write(i);
        foreach (var i in new C()) Console.Write(i);
        Console.WriteLine();
    }
}
"#,
        "123123123\n",
    );
}

#[test]
fn ref_returning_arguments_moved_ahead_of_a_call_stay_references() {
    check(
        "RefArgumentsInWrittenOrder",
        r#"
struct S
{
    public readonly int x;
    public S(int x) { this.x = x; }
    static S[] arr = { new S() };
    static ref S I(int value) { arr[0] = new S(value); return ref arr[0]; }
    static void M(in S first, in S second) => System.Console.Write(second.x);
    static void Main()
    {
        // Both arguments are the one element, written 5 and then 3.
        M(second: I(5), first: I(3));
        System.Console.WriteLine();
    }
}
"#,
        "3\n",
    );
}

#[test]
fn field_in_an_indexer_is_the_member_of_that_name() {
    // C# 14 gives a property's accessors a `field`, but not an indexer's.
    check(
        "FieldInAnIndexer",
        r#"
class D
{
    object field = null;
    public ref object this[int i] { get => ref field; }
    static void Main()
    {
        var d = new D();
        System.Console.WriteLine(d[0] ??= "set");
        System.Console.WriteLine(d.field);
    }
}
"#,
        "set\nset\n",
    );
}

#[test]
fn a_delegate_made_with_ref_or_out_on_its_argument_and_a_ref_struct_behind_a_question_dot() {
    check(
        "DelegateArgumentsAndRefLikes",
        r#"
using System;
class C
{
    static void M() => Console.Write("m ");
    public R Make() { Console.Write("made "); return default; }
    public ref struct R { }
    static void Main()
    {
        Action a = new Action(ref M);
        a();
        Action b = new Action(out a);
        b();
        C c = new C();
        c?.Make();
        c = null;
        c?.Make();
        Console.WriteLine();
    }
}
"#,
        "m m made \n",
    );
}

#[test]
fn a_com_import_interface_takes_arguments_without_the_ref_its_parameters_have() {
    check(
        "ComRefOmitted",
        r#"
using System;
using System.Runtime.InteropServices;
[ComImport]
[Guid("A88A175D-2448-447A-B786-64682CBEF156")]
public interface IRef1
{
    int M(ref int x, int y);
}
public class Ref1Impl : IRef1
{
    public int M(ref int x, int y) { x = 100; return x + y; }
}
class Test
{
    static void Main()
    {
        IRef1 ref1 = new Ref1Impl();
        int x = 1;
        // A copy of `x` goes by reference, and `x` keeps its value.
        Console.Write(ref1.M(x, 10) + " " + x + " ");
        Console.Write(ref1.M(10, 10) + " ");
        Console.WriteLine(ref1.M(ref x, 1) + " " + x);
    }
}
"#,
        "110 1 110 101 100\n",
    );
}

#[test]
fn a_lambda_with_a_function_pointer_parameter_has_a_delegate_type_of_its_own() {
    check(
        "FunctionPointerLambda",
        r#"
using System;
unsafe class Program
{
    static void Main()
    {
        var d = (delegate*<void> f) => Console.Write((int)f + " ");
        d((delegate*<void>)4);
        Console.WriteLine(d.GetType().Name);
    }
}
"#,
        "4 <>f__AnonymousDelegate0\n",
    );
}

#[test]
fn a_bare_default_sizes_indexes_and_filters() {
    check(
        "DefaultLiteralPlaces",
        r#"
class C
{
    static void Main()
    {
        var a = new int[default];
        int[] x = { 1, 2 };
        System.Console.Write(a.Length + " " + x[default] + " ");
        try
        {
            try { throw new System.Exception(); }
            catch (System.Exception) when (default) { System.Console.Write("unreachable "); }
        }
        catch { System.Console.WriteLine("outer"); }
    }
}
"#,
        "0 1 outer\n",
    );
}

#[test]
fn foreach_walks_every_dimension_of_an_array_of_pointers() {
    check(
        "MultidimensionalForEach",
        r#"
using System;
unsafe class C
{
    static void Main()
    {
        int*[,] pointers = { { (int*)1, (int*)2 }, { (int*)3, (int*)4 } };
        foreach (var p in pointers) Console.Write((int)p);
        int[,,] numbers = new int[2, 2, 2] { { { 1, 2 }, { 3, 4 } }, { { 5, 6 }, { 7, 8 } } };
        foreach (int n in numbers)
        {
            if (n == 2) continue;
            if (n == 7) break;
            Console.Write(n);
        }
        Console.WriteLine();
    }
}
"#,
        "123413456\n",
    );
}

#[test]
fn extern_aliases_tell_apart_types_of_the_same_name_from_different_libraries() {
    check_with_aliased_libraries(
        "ExternAliases",
        &[
            (
                "namespace NS1 { public static class C1 { public static string M1(this string x) => \"C1\"; } }",
                &[],
            ),
            (
                "namespace NS2 { public static class C2 { public static string M1(this string x) => \"C2\"; } }\npublic class Same { public static string Who => \"first\"; public Same() { } }",
                &["first"],
            ),
            (
                "public class Same { public static string Who => \"second\"; }",
                &["second"],
            ),
        ],
        r#"
extern alias first;
extern alias second;
using first::NS2;
class Program
{
    static void Main()
    {
        System.Console.WriteLine("x".M1() + " " + first::Same.Who + " " + second::Same.Who
            + " " + new first::Same().GetType().Assembly.GetName().Name);
    }
}
"#,
        "C2 first second ExternAliasesLibrary1\n",
    );
}

#[test]
fn ref_fields_are_set_in_initializers_read_through_and_written_through_readonly_refs() {
    check(
        "RefFields",
        r#"
using System;
ref struct R
{
    public ref int field;
    public readonly ref int fixedTo;
    public R(ref int to) { fixedTo = ref to; }
    public override string ToString() => field.ToString();
}
class C
{
    static void Main()
    {
        int x = 42, y = 1;
        var r = new R(ref y) { field = ref x };
        Console.Write(r.ToString() + " ");
        r.fixedTo = 7;
        scoped var s = new R(ref x);
        s.fixedTo++;
        Console.WriteLine(y + " " + x);
    }
}
"#,
        "42 7 43\n",
    );
}

#[test]
fn an_argument_moved_ahead_of_a_call_across_an_await_is_spilled_by_value() {
    check(
        "InArgumentsAcrossAwait",
        r#"
using System.Threading.Tasks;
class Program
{
    static void Main() => Test().Wait();
    static async Task Test()
    {
        int local = 1;
        M1(arg3: 3, arg1: RefReturning(ref local), arg2: await Get(2));
    }
    static ref int RefReturning(ref int arg) => ref arg;
    static async Task<int> Get(int value) { await Task.Yield(); return value; }
    static void M1(in int arg1, in int arg2, in int arg3) => System.Console.WriteLine(arg1 + arg2 + arg3);
}
"#,
        "6\n",
    );
}

#[test]
fn a_pointer_converts_to_a_native_integer_by_the_language_checked_or_not() {
    check(
        "PointerToNativeInteger",
        r#"
using System;
class C
{
    public unsafe static void Main()
    {
        void* ptr = (void*)ulong.MaxValue;
        try { IntPtr i = checked((IntPtr)ptr); }
        catch (OverflowException) { Console.Write("overflow "); }
        IntPtr j = unchecked((IntPtr)ptr);
        Console.WriteLine(j == (IntPtr)(-1));
    }
}
"#,
        "overflow True\n",
    );
}

#[test]
fn custom_modifiers_of_a_library_are_repeated_copied_and_checked() {
    // `M` takes an `int` under a `modopt`, which a call has to name again
    // and an override has to copy. `Child.N` left out the `modreq` its `in`
    // parameter needs on a virtual method, so C# cannot call it and the call
    // is the base's — which the runtime dispatches to the base, since the
    // two signatures differ.
    check_with_il_library(
        "CustomModifiers",
        r#"
.class public auto ansi beforefieldinit Parent extends [mscorlib]System.Object
{
    .method public hidebysig newslot virtual instance string M(int32 modopt([mscorlib]System.Runtime.CompilerServices.IsConst) x) cil managed
    { ldstr "Parent.M" ret }
    .method public hidebysig newslot virtual instance string N([in] int32& modreq([mscorlib]System.Runtime.InteropServices.InAttribute) x) cil managed
    {
        .param [1]
        .custom instance void [mscorlib]System.Runtime.CompilerServices.IsReadOnlyAttribute::.ctor() = (01 00 00 00)
        ldstr "Parent.N" ret
    }
    .method public hidebysig specialname rtspecialname instance void .ctor() cil managed
    { ldarg.0 call instance void [mscorlib]System.Object::.ctor() ret }
}
.class public auto ansi beforefieldinit Child extends Parent
{
    .method public hidebysig virtual instance string N([in] int32& x) cil managed
    {
        .param [1]
        .custom instance void [mscorlib]System.Runtime.CompilerServices.IsReadOnlyAttribute::.ctor() = (01 00 00 00)
        ldstr "Child.N" ret
    }
    .method public hidebysig specialname rtspecialname instance void .ctor() cil managed
    { ldarg.0 call instance void Parent::.ctor() ret }
}
"#,
        r#"
using System;
class Derived : Parent
{
    public override string M(int x) => "Derived.M";
}
class Program
{
    static void Main()
    {
        Parent derived = new Derived();
        Console.WriteLine(new Parent().M(1) + " " + derived.M(2) + " " + new Child().N(3));
    }
}
"#,
        "Parent.M Derived.M Parent.N\n",
    );
}

#[test]
fn a_left_out_argument_takes_the_default_a_library_wrote() {
    check_with_library(
        "LibraryDefaults",
        r#"
public enum Kind { A, B, C }
public static class Library
{
    public static string F(int x = 7, string s = "d", double d = 1.5, Kind k = Kind.C, object o = null, char c = 'z')
        => x + " " + s + " " + d + " " + k + " " + (o == null) + " " + c;
}
"#,
        r#"
class Program
{
    static void Main() => System.Console.WriteLine(Library.F() + " | " + Library.F(1, s: "e"));
}
"#,
        "7 d 1.5 C True z | 1 e 1.5 C True z\n",
    );
}

/// `ilasm`, where there is one: `RUSTLYN_ILASM`, or where `tools/cav/setup.sh`
/// puts it.
fn ilasm() -> Option<PathBuf> {
    std::env::var("RUSTLYN_ILASM")
        .map(PathBuf::from)
        .ok()
        .or_else(|| Some(PathBuf::from("/home/user/ilasm/ilasm")))
        .filter(|path| path.is_file())
}

/// As [`check_with_library`], with the library written in IL and assembled
/// by `ilasm`: what C# cannot write, such as a `modopt`.
#[track_caller]
fn check_with_il_library(name: &str, il: &str, source: &str, expected: &str) {
    let (Some(mut bytes), Some(ilasm)) = (references(), ilasm()) else {
        println!("note: {name} was skipped; no .NET shared framework or no ilasm was found");
        return;
    };
    let directory = scratch(name);
    let library_name = format!("{name}Library");
    let il_path = directory.join(format!("{library_name}.il"));
    let dll_path = directory.join(format!("{library_name}.dll"));
    let header = format!(
        ".assembly '{library_name}' {{}}\n.assembly extern mscorlib {{ .publickeytoken = (B7 7A 5C 56 19 34 E0 89) .ver 4:0:0:0 }}\n"
    );
    std::fs::write(&il_path, header + il).expect("the IL should be writable");
    let status = std::process::Command::new(ilasm)
        .arg("-dll")
        .arg("-quiet")
        .arg(format!("-output={}", dll_path.display()))
        .arg(&il_path)
        .status()
        .expect("ilasm should run");
    assert!(status.success(), "{name}: ilasm refused the library");
    bytes.push(std::fs::read(&dll_path).expect("the library should be readable"));
    let compilation = compiled(name, source, &bytes);
    let emitted = rustlyn_emit::emit(&compilation, name)
        .unwrap_or_else(|error| panic!("{name} could not be emitted: {error}"));
    run_emitted(name, &directory, &emitted, expected);
}

/// As [`check_with_library`], with several libraries, each referenced under
/// the `extern alias`es given with it (none for the global namespace).
#[track_caller]
fn check_with_aliased_libraries(
    name: &str,
    libraries: &[(&str, &[&str])],
    source: &str,
    expected: &str,
) {
    let Some(mut bytes) = references() else {
        println!("note: {name} was skipped; no .NET shared framework was found");
        return;
    };
    let directory = scratch(name);
    // Each library is compiled against the framework alone.
    let framework = bytes.len();
    let mut aliases: Vec<Vec<String>> = vec![Vec::new(); framework];
    for (at, (library, named)) in libraries.iter().enumerate() {
        let library_name = format!("{name}Library{at}");
        let compilation = compiled(&library_name, library, &bytes[..framework]);
        let emitted = rustlyn_emit::emit_library(&compilation, &library_name)
            .unwrap_or_else(|error| panic!("{library_name} could not be emitted: {error}"));
        std::fs::write(
            directory.join(format!("{library_name}.dll")),
            &emitted.assembly,
        )
        .expect("the library should be writable");
        bytes.push(emitted.assembly);
        aliases.push(named.iter().map(|alias| (*alias).to_string()).collect());
    }
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
    let compilation = Compilation::create_with_aliased_references(
        vec![parse(SourceText::new("Program.cs", source))],
        &images,
        &aliases,
    );
    let diagnostics: Vec<String> = compilation
        .source_diagnostics()
        .into_iter()
        .map(|entry| compilation.render(entry))
        .chain(
            compilation
                .semantic_diagnostics()
                .iter()
                .map(|entry| compilation.render(entry)),
        )
        .collect();
    assert!(
        diagnostics.is_empty(),
        "{name} did not compile: {diagnostics:#?}"
    );
    let emitted = rustlyn_emit::emit(&compilation, name)
        .unwrap_or_else(|error| panic!("{name} could not be emitted: {error}"));
    run_emitted(name, &directory, &emitted, expected);
}

#[test]
fn defaults_a_library_writes_are_read_back_and_decimals_are_attributes() {
    check_with_library(
        "metadata_defaults",
        r#"
using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
public class L
{
    public const decimal Rate = -1.25m;
    public static string M(int x = 5, string s = "hi", decimal d = 1.5m) => x + s + d;
    public static long When([Optional, DateTimeConstant(42L)] DateTime d) => d.Ticks;
}
"#,
        r#"
using System;
using System.Reflection;
class P
{
    const decimal Twice = L.Rate;
    public int this[in int x] => 1;
    public int this[int x] => 2;
    static void Hello() => Console.Write("hello ");
    static void Main()
    {
        Console.Write(L.M() + " " + L.When() + " " + Twice + " ");
        var field = typeof(L).GetField("Rate");
        Console.Write(field.IsInitOnly + " " + field.GetCustomAttributesData().Count + " ");
        var p = new P();
        int i = 3;
        Console.Write(p[i] + " " + p[in i] + " ");
        Action a = new Action(ref Hello);
        a();
    }
}
"#,
        "5hi1.5 42 -1.25 True 1 2 1 hello ",
    );
}

#[test]
fn a_com_call_may_leave_out_ref() {
    check(
        "com_ref_omitted",
        r#"
using System;
using System.Globalization;
using System.Runtime.InteropServices;
[ComImport]
[Guid("A88A175D-2448-447A-B786-64682CBEF156")]
public interface IRef1 { int M(ref int x, int y); }
public class Ref1Impl : IRef1 { public int M(ref int x, int y) { x = 100; return x + y; } }
class Test
{
    static void Main()
    {
        IRef1 ref1 = new Ref1Impl();
        int x = 10;
        Console.Write(ref1.M(x, 1) + " " + x + " ");
    }
}
"#,
        "101 10 ",
    );
}

/// A varargs method and a call to it: `__arglist` in the parameter list and
/// at the call. The runtime on this platform does not run the vararg calling
/// convention, so the program is only compiled and emitted.
#[test]
fn a_varargs_method_and_its_call_site_are_emitted() {
    let Some(bytes) = references() else {
        return;
    };
    let compilation = compiled(
        "varargs",
        r#"
using System;
class C
{
    static int M(int x, __arglist) => new ArgIterator(__arglist).GetRemainingCount() + x;
    static void Main() { Console.Write(M(1, __arglist(2, "three"))); }
}
"#,
        &bytes,
    );
    rustlyn_emit::emit(&compilation, "varargs")
        .unwrap_or_else(|error| panic!("varargs could not be emitted: {error}"));
}

/// Named arguments are read into each candidate's own parameters before the
/// candidates are compared (§12.6.2.2): `Bar(x: 1, y: "")` reaches `Bar(string
/// y, int x)` as well as `Bar(int x, string y, params int[] z)`, and the first
/// wins as the normal form. A partial method is called by the names of its
/// declaring part, and metadata keeps them, while its body goes by its own.
#[test]
fn named_arguments_are_placed_per_candidate() {
    check(
        "named_per_candidate",
        r#"
using System;
using System.Reflection;
static partial class P
{
    static int Bar(int x, string y, params int[] z) { return 1; }
    static int Bar(string y, int x) { return 0; }
    static int Goo<T>(int x, T y) { return 1; }
    static int Goo<T>(string y, int x) { return 0; }
    static void Method(int a, int b) { Console.Write("val " + a + b + " "); }
    static void Method(in int b, int a) { Console.Write("in " + b + a + " "); }
    static partial void M<T, U>(T x, U y);
    static partial void M<T1, T2>(T1 y, T2 x)
    {
        Console.Write(x + "," + y + " ");
        var m = typeof(P).GetMethod("M", BindingFlags.Static | BindingFlags.NonPublic);
        Console.Write(m.GetGenericArguments()[0].Name + m.GetParameters()[0].Name + " ");
    }
    static void Main()
    {
        Console.Write(Bar(x: 1, y: "T0"));
        Console.Write(Goo<string>(x: 1, y: "T2") + " ");
        int a = 1, b = 2;
        Method(b: b, a: a);
        Method(a: a, b: in b);
        M(x: 1, y: 2);
    }
}
"#,
        "00 val 12 in 21 2,1 Tx ",
    );
}

/// Before C# 10 a lambda that returns a lambda infers no return type, so it
/// matches no delegate exactly and what it says gives way to the other
/// arguments: `M1(() => () => i, i)` is the `(DB, int)` overload in C# 9 and
/// the `(DA, object)` one from C# 10 on.
#[test]
fn a_lambda_returning_a_lambda_has_no_return_type_before_csharp_10() {
    let source = r#"
using System;
class P
{
    delegate Func<int> DA();
    delegate Func<object> DB();
    static void M1(DA a, object b) { Console.Write(1); }
    static void M1(DB a, int b) { Console.Write(2); }
    static void Main()
    {
        int i = 0;
        M1(() => () => i, i);
    }
}
"#;
    use rustlyn_syntax::LanguageVersion;
    let options = rustlyn_semantics::CompilationOptions::default();
    check_with_options(
        "NestedLambda9",
        LanguageVersion::CSharp9,
        options.clone(),
        source,
        "2",
    );
    check_with_options(
        "NestedLambda10",
        LanguageVersion::CSharp10,
        options,
        source,
        "1",
    );
}

/// An `await` among the arguments leaves a receiver of a type parameter as
/// it was when the call began where the type turns out a class (a copy is
/// kept), and the variable itself where it is a struct. A compound
/// assignment reads its target before the `await`, `??=` awaits only where
/// the target was null, `item[^i]` counts from the receiver kept, and an
/// element of a `T[]` of a class is read as a copy — the array may be of a
/// derived type.
#[test]
fn an_await_among_the_arguments_keeps_a_generic_receiver() {
    check(
        "await_generic_receiver",
        r#"
using System;
using System.Threading.Tasks;
interface IMoveable { void GetName(int x); int Position { get; set; } int? Maybe { get; set; } int this[int i] { get; set; } int Length { get; } }
class Item : IMoveable
{
    public string Name;
    public void GetName(int x) => Console.Write("call" + Name + " ");
    public int Position { get { Console.Write("get" + Name + " "); return 0; } set => Console.Write("set" + Name + " "); }
    public int? Maybe { get { Console.Write("maybe" + Name + " "); return null; } set => Console.Write("put" + Name + " "); }
    public int this[int i] { get { Console.Write("at" + Name + " "); return 0; } set => Console.Write("store" + Name + " "); }
    public int Length { get { Console.Write("length" + Name + " "); return 1; } }
}
class Derived : Item { }
struct Value : IMoveable
{
    public string Name;
    public void GetName(int x) => Console.Write("call" + Name + " ");
    public int Position { get { Console.Write("get" + Name + " "); return 0; } set => Console.Write("set" + Name + " "); }
    public int? Maybe { get { Console.Write("maybe" + Name + " "); return null; } set => Console.Write("put" + Name + " "); }
    public int this[int i] { get { Console.Write("at" + Name + " "); return 0; } set => Console.Write("store" + Name + " "); }
    public int Length { get { Console.Write("length" + Name + " "); return 1; } }
}
class Program
{
    static int next;
    static int Replace<T>(ref T item) { item = (T)(IMoveable)(typeof(T) == typeof(Value) || item is Value ? new Value { Name = "v" + ++next } : new Item { Name = "i" + ++next }); return 0; }
    static int ReplaceFirst<T>(ref T[] items) { items[0] = (T)(IMoveable)new Derived { Name = "d" + ++next }; return 0; }
    static async Task<int> Later(int i) { await Task.Yield(); return i; }
    static async Task Run<T>(T item) where T : IMoveable
    {
        item.GetName(await Later(Replace(ref item)));
        item.Position += await Later(Replace(ref item));
        item.Maybe ??= await Later(Replace(ref item));
        item[^await Later(Replace(ref item))] += 1;
        Console.WriteLine();
    }
    static async Task Run<T>(T[] items) where T : IMoveable
    {
        items[0].GetName(await Later(ReplaceFirst(ref items)));
        Console.WriteLine();
    }
    static async Task Main()
    {
        await Run<IMoveable>(new Item { Name = "a" });
        await Run(new Item { Name = "b" });
        await Run(new Value { Name = "c" });
        await Run((Item[])new Derived[] { new Derived { Name = "e" } });
    }
}
"#,
        "calla geti1 seti1 maybei2 puti2 lengthi3 ati3 storei3 \n\
         callb geti5 seti5 maybei6 puti6 lengthi7 ati7 storei7 \n\
         callv9 getv9 setv10 maybev10 putv11 lengthv12 atv12 storev12 \n\
         calle \n",
    );
}

/// A method group's natural type is read off the method an override
/// overrides, which is where `params` is declared: `new D().M` is the
/// synthesized delegate with a `params long[]`. Converting the group, the
/// derived type's own generic `M<T>` puts out the override, which counts as
/// its base's.
#[test]
fn a_method_group_is_typed_by_the_least_overridden_method() {
    check(
        "least_overridden_group",
        r#"
var c = ((C<long>)new D()).M;
System.Console.WriteLine(c.GetType());
c(null);
var m = new D().M;
System.Console.WriteLine(m.GetType());
m(null);
abstract class C<T>
{
    public abstract void M(params T[] xs);
}
class D : C<long>
{
    public override void M(long[] xs) => System.Console.WriteLine("A");
    public void M<T>(T[] xs) => System.Console.WriteLine("B");
}
"#,
        "<>f__AnonymousDelegate0`1[System.Int64]\nA\n<>f__AnonymousDelegate0`1[System.Int64]\nB\n",
    );
}

/// A lambda beside a delegate takes that delegate's type: in an array, where
/// the lambda's function type converts to any delegate of its signature, in
/// a conditional, parenthesized or not, and compared with `==`, where a
/// lambda or a method group is a value of its natural type.
#[test]
fn a_lambda_beside_a_delegate_takes_its_type() {
    check(
        "lambda_beside_delegate",
        r#"
using System;
delegate int StringIntDelegate(string s);
class Program
{
    static int M(string s) => s.Length;
    static void Main()
    {
        bool b = false;
        StringIntDelegate d = M;
        var a = new[] { (string s) => int.Parse(s), d };
        Console.Write(a[0].GetType().Name + " ");
        var c = b ? ((string s) => int.Parse(s)) : d;
        Console.Write(c.GetType().Name + " ");
        var e = (() => { }) == null;
        var f = Main == (() => { });
        Console.Write(e + " " + f);
    }
}
"#,
        "StringIntDelegate StringIntDelegate False False",
    );
}

/// A lambda whose body is a statement expression is as good an `Action` as
/// any, so `F(() => i++)` is `F(Action)` rather than `F<T>` with `T` from the
/// lambda's natural type; `() => (c.Clone())` is a value, and no `Action`.
/// A type argument inferred from a typed argument is no natural type, even
/// where a lambda beside it has one.
#[test]
fn a_statement_lambda_is_an_action_before_a_natural_type() {
    check(
        "statement_lambda_action",
        r#"
using System;
class A { }
class B : A { }
class Program
{
    static void F(Action action) => Console.Write("Action ");
    static void F<T>(T t) => Console.Write(typeof(T).Name + " ");
    static void Goo(Action x, string y) => Console.Write("Action ");
    static void Goo(Func<object> x, object y) => Console.Write("Func ");
    static void M<T>(T x, T y) => Console.Write("M<T> ");
    static void M(Func<object> x, Func<object> y) => Console.Write("M ");
    static void Main()
    {
        int i = 0;
        F(() => i++);
        ICloneable c = "";
        Goo(() => (c.Clone()), null);
        Func<A> fa = () => new A();
        M(fa, () => new B());
        M(() => new A(), () => new B());
    }
}
"#,
        "Action Func M<T> M ",
    );
}

/// A compound assignment through a user-defined operator is written out as
/// the operator's call and a store, for `this` in a struct as for a local,
/// and for a property, a field of another object, an indexer and an array
/// element, whose receivers and indices are evaluated once.
#[test]
fn a_compound_assignment_calls_the_user_defined_operator_on_any_place() {
    check(
        "compound_user_defined_places",
        r#"
using System;
struct V
{
    public int X;
    public V(int x) { X = x; }
    public static V operator +(V a, int b) => new V(a.X + b);
    public override string ToString() => X.ToString();
    public void Twice() { this += X; }
}
class H
{
    public V P { get; set; }
    public V F;
    V[] items = new V[3];
    public V this[int i] { get => items[i]; set => items[i] = value; }
}
class Program
{
    static int calls;
    static H Get(H h) { calls++; return h; }
    static int Index() { calls++; return 1; }
    static void Main()
    {
        var h = new H();
        Get(h).P += 2;
        Get(h).F += 3;
        Get(h)[Index()] += 4;
        var arr = new V[2];
        arr[Index()] += 5;
        var v = new V(6);
        v.Twice();
        Console.Write(h.P + " " + h.F + " " + h[1] + " " + arr[1] + " " + calls + " " + v);
    }
}
"#,
        "2 3 4 5 5 12",
    );
}

/// A cast reaches a user-defined explicit operator through a down-cast on
/// either side: `(F)d` on a `D : B` calls `explicit operator E(B)` and casts
/// the `E` it gives to `F : E` — `D` and `F` have no reference conversion.
#[test]
fn a_cast_reaches_an_explicit_operator_through_a_down_cast() {
    check(
        "explicit_operator_down_cast",
        r#"
using System;
class B
{
    public string str;
    public B(string s) { str = s; }
    public static explicit operator E(B b) { return new F(b.str); }
}
class D : B { public D(string s) : base(s) { } }
class E { public string str; public E(string s) { str = s; } }
class F : E { public F(string s) : base(s) { } public override string ToString() => "F" + str; }
class C
{
    static void Main()
    {
        D d = new D("y");
        F f = (F)d;
        Console.Write(f);
    }
}
"#,
        "Fy",
    );
}

/// A cast of a tuple to a nullable tuple converts it element by element —
/// by the explicit down-cast that a user-defined implicit operator does not
/// get to pass over — and wraps what that makes.
#[test]
fn a_tuple_cast_to_a_nullable_tuple_converts_its_elements() {
    check(
        "tuple_to_nullable_tuple",
        r#"
using System;
class C<T> { }
class D<T> : C<T>
{
    readonly string val;
    public D(string val) { this.val = val; }
    public override string ToString() => val;
    public static implicit operator D<T>(C<int> x) => new D<T>("converted");
}
class B
{
    static void Main()
    {
        (C<int>, C<int>) xt = (new D<int>("a"), new D<int>("b"));
        (D<int>, D<int>)? cast = ((D<int>, D<int>)?)xt;
        (D<int>, D<int>)? assigned = xt;
        Console.Write(cast + " " + assigned);
    }
}
"#,
        "(a, b) (converted, converted)",
    );
}

/// An indexer reached through a variable of a type parameter keeps the
/// receiver it began with where the type is a class, and counts `^i` from
/// that receiver's `Length`; a deconstruction evaluates its targets'
/// receivers and indices before the right-hand side, in the same way.
#[test]
fn a_generic_indexer_receiver_is_kept_before_its_index() {
    check(
        "generic_indexer_receiver",
        r#"
using System;
interface IMoveable { int this[int i] { get; set; } int Length { get; } int Position { get; set; } }
class Item : IMoveable
{
    public string Name;
    public int this[int i] { get { Console.Write("get" + Name + " "); return 0; } set => Console.Write("set" + Name + " "); }
    public int Length { get { Console.Write("length" + Name + " "); return 1; } }
    public int Position { get => 0; set => Console.Write("position" + Name + " "); }
}
class Program
{
    static int next;
    static int Replace<T>(ref T item) { item = (T)(IMoveable)new Item { Name = "" + ++next }; return 0; }
    static void Read<T>(T item) where T : IMoveable { _ = item[^Replace(ref item)]; }
    static void Take<T>(T item) where T : IMoveable { (item.Position, _) = (Replace(ref item), 1); }
    static void TakeAt<T>(T item) where T : class, IMoveable { (item[^1], _) = (Replace(ref item), 0); }
    static void Main()
    {
        Read(new Item { Name = "a" });
        Take(new Item { Name = "b" });
        TakeAt(new Item { Name = "c" });
    }
}
"#,
        "lengtha geta positionb lengthc setc ",
    );
}

/// `item[range]` on a variable of a struct, or of a `T` that turns out one,
/// slices the variable itself once the range is worked out; a `T` that turns
/// out a class slices the instance it held first.
#[test]
fn a_range_slices_a_struct_variable_after_the_range() {
    check(
        "range_struct_variable",
        r#"
using System;
interface IMoveable { IMoveable Slice(int start, int length); int Length { get; } }
struct Item : IMoveable
{
    public string Name;
    public IMoveable Slice(int start, int length) { Console.Write("slice" + Name + " "); return this; }
    public int Length { get { Console.Write("length" + Name + " "); return 2; } }
}
class Box : IMoveable
{
    public string Name;
    public IMoveable Slice(int start, int length) { Console.Write("slice" + Name + " "); return this; }
    public int Length { get { Console.Write("length" + Name + " "); return 2; } }
}
class Program
{
    static int next;
    static Range Replace<T>(ref T item)
    {
        item = item is Item ? (T)(IMoveable)new Item { Name = "" + ++next } : (T)(IMoveable)new Box { Name = "" + ++next };
        return 0..1;
    }
    static void Cut<T>(T item) where T : IMoveable { _ = item[Replace(ref item)]; }
    static void CutStruct<T>(T item) where T : struct, IMoveable { _ = item[Replace(ref item)]; }
    static void Main()
    {
        Cut(new Item { Name = "a" });
        CutStruct(new Item { Name = "b" });
        Cut(new Box { Name = "c" });
    }
}
"#,
        "length1 slice1 length2 slice2 lengthc slicec ",
    );
}

/// An enum's arithmetic is as narrow as the enum: `~e` on a `ushort` enum
/// and `E - E` on a `byte` one keep only their own bits, in a `checked`
/// region too. A protected constructor is no candidate outside its type and
/// the types derived from it.
#[test]
fn enum_arithmetic_is_narrow_and_protected_constructors_are_not_candidates() {
    check(
        "narrow_enum_protected_ctor",
        r#"
using System;
public class A
{
    protected A(int x) { Console.Write("int "); }
    public A(long x) { Console.Write("long "); }
}
class Program
{
    enum E : ushort { one = 1 }
    enum B : byte { a = 0, c = 1 }
    static void Main()
    {
        checked
        {
            E e = E.one;
            Console.Write(5 + (int)~e + " ");
        }
        int j = ((Func<B>)(() => B.a))() - B.c;
        Console.Write(j + " ");
        new A(1);
    }
}
"#,
        "65539 255 long ",
    );
}

/// A variable written `ref` goes only to a parameter of its very type; and
/// where two candidates of a COM interface both leave out a `ref`, an
/// argument taken by value is the better only where it goes in as it is.
#[test]
fn com_candidates_that_both_omit_ref_are_compared_by_ref_kind() {
    check(
        "com_ref_kinds",
        r#"
using System;
using System.Runtime.InteropServices;
[ComImport]
[Guid("A88A175D-2448-447A-B786-64682CBEF156")]
public interface IRef1
{
    void M8(long x, ref int y);
    void M8(ref long x, int y);
    void M9(ref long x, ref int y);
    void M9(ref int x, ref long y);
}
public class Ref1Impl : IRef1
{
    public void M8(long x, ref int y) { Console.Write(15 + " "); }
    public void M8(ref long x, int y) { Console.Write(16 + " "); }
    public void M9(ref long x, ref int y) { Console.Write(17 + " "); }
    public void M9(ref int x, ref long y) { Console.Write(18 + " "); }
}
class Test
{
    static void Main()
    {
        IRef1 ref1 = new Ref1Impl();
        int i = 1;
        char c = 'c';
        ref1.M8(i, i);
        ref1.M8(c, i);
        ref1.M9(ref i, i);
        ref1.M9(ref i, c);
    }
}
"#,
        "16 16 18 18 ",
    );
}

/// A lambda asked what it returns while the callee's type arguments are
/// still being inferred answers from its body alone: `() => null` beside
/// `() => new A()` for two `Func<R>` says nothing about `R`, whichever comes
/// first. As an expression tree its `null` is a constant of the delegate's
/// return type.
#[test]
fn a_lambda_returning_null_leaves_inference_to_the_others() {
    check(
        "lambda_null_inference",
        r#"
using System;
using System.Linq.Expressions;
class A { }
static class X
{
    static void L<R>(Func<R> a, Func<R> b) { Console.Write(typeof(R).Name + " "); }
    static void T<R>(Expression<Func<R>> a, Expression<Func<R>> b) { Console.Write(a.Compile()() == null); }
    static void Main()
    {
        L(() => null, () => new A());
        L(() => new A(), () => null);
        T(() => null, () => new A());
    }
}
"#,
        "A A True",
    );
}

#[test]
fn a_com_call_that_leaves_out_a_ref_ranks_below_one_that_does_not() {
    // `M(I1, ref int)` takes `x` only by leaving its `ref` out, so the
    // `in` overload wins even though `null` fits either interface.
    check(
        "ComRefOmittedRanksLower",
        r#"
using System.Runtime.InteropServices;
interface I1 { }
interface I2 { }
[ComImport, Guid("96A2DE64-6D44-4DA5-BBA4-25F5F07E0E6B")]
interface I
{
    void M(I1 o, ref int i);
    void M(I2 o, in int i);
}
class C : I
{
    void I.M(I1 o, ref int i) => System.Console.Write("1");
    void I.M(I2 o, in int i) => System.Console.Write("2");
}
class Program
{
    static void Main()
    {
        I i = new C();
        int x = 42;
        i.M(null, 43);
        i.M(null, x);
        i.M(null, in x);
        i.M(null, ref x);
        System.Console.WriteLine();
    }
}
"#,
        "2221\n",
    );
}

#[test]
fn a_method_called_through_a_ref_readonly_field_runs_on_a_copy() {
    check(
        "RefReadonlyFieldReceiver",
        r#"
using System;
class Program
{
    static void Main()
    {
        S s = new();
        M(in s);
        Console.Write(s + " ");
        W(ref s);
        Console.WriteLine(s);
    }
    static void M(in S s)
    {
        R r = new(in s);
        r.S.M();
    }
    static void W(ref S s)
    {
        RW r = new(ref s);
        r.S.M();
    }
}
struct S
{
    int i;
    public void M() { i++; }
    public readonly override string ToString() => i.ToString();
}
ref struct R
{
    public ref readonly S S;
    public R(in S s) { S = ref s; }
}
ref struct RW
{
    public ref S S;
    public RW(ref S s) { S = ref s; }
}
"#,
        "0 1\n",
    );
}

#[test]
fn a_ref_readonly_parameter_names_its_delegate_apart_from_in() {
    check(
        "RefReadonlyDelegateName",
        r#"
class Program
{
    static void Main()
    {
        var a = (ref readonly int p) => { };
        var b = (in int p) => { };
        System.Console.WriteLine(a.GetType() + " " + b.GetType());
        System.Console.WriteLine(
            typeof(Program).GetMethod(nameof(M)).GetParameters()[0].GetCustomAttributes(false)[0]);
    }
    public static void M(ref readonly int p) { }
}
"#,
        "<>A{00000004}`1[System.Int32] <>A{00000003}`1[System.Int32]\n\
         System.Runtime.CompilerServices.RequiresLocationAttribute\n",
    );
}

#[test]
fn decimal_and_date_time_defaults_come_from_their_attributes() {
    check_with_library(
        "AttributedDefaults",
        r#"
public static class L
{
    public static decimal Written(decimal d = 1.10m) => d;
}
"#,
        r#"
using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
class Program
{
    static decimal D([Optional, DecimalConstant(0, 0, low: (uint)100, mid: (uint)0, hi: (uint)0)] decimal d) => d;
    static int I([Optional, DecimalConstant(0, 0, 0u, 0u, 50u)] int i) => i;
    static long T([Optional, DateTimeConstant(100)] DateTime t) => t.Ticks;
    static string S([Optional, DateTimeConstant(100)] string s) => s ?? "null";
    static void Main()
    {
        Console.WriteLine(D() + " " + I() + " " + T() + " " + S() + " " + L.Written());
        var a = ([Optional, DecimalConstant(1, 0, 0u, 0u, 11u)] decimal d) => d;
        var b = (decimal d = 1.1m) => d;
        Console.WriteLine(a() + " " + b() + " " + (a.GetType() == b.GetType()));
    }
}
"#,
        "100 50 100 null 1.10\n1.1 1.1 True\n",
    );
}

#[test]
fn in_arguments_stay_the_variables_they_name() {
    // Moved ahead of the call by a named argument, given to a setter, or
    // the receiver a `ref readonly` return hands back: each is the
    // variable itself, and sees what is written to it before the call.
    check(
        "InArgumentsStayVariables",
        r#"
using System;
class C
{
    public struct S { public int X; }
    static S _field;
    static int _f = 1;
    static ref S GetField() { _field.X++; return ref _field; }
    static void M(in int x, in int y, in int z) => Console.Write(x + " " + y + " " + z + " ");
    public int this[in int x, int y = 0]
    {
        get => x;
        set { _f++; Console.Write(x + " "); }
    }
    static ref readonly R GetR(ref R r) { r = new R(r.F + 1); return ref r; }
    static void Main()
    {
        M(y: in GetField().X, z: GetField().X, x: GetField().X);
        new C()[in _f] = 0;
        var r = new R();
        GetR(ref r).Show(GetR(ref r).F);
        Console.WriteLine();
    }
}
public readonly struct R
{
    public readonly int F;
    public R(int f) { F = f; }
    public void Show(in int other) => Console.Write(F + " " + other);
}
"#,
        "3 3 3 2 2 2\n",
    );
}

#[test]
fn a_call_that_may_change_an_in_receiver_runs_on_a_copy() {
    check(
        "InReceiverCopied",
        r#"
using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
interface I { void Bump(); }
public struct S : IEnumerable<int>, I
{
    public int A;
    public void Bump() { A++; }
    IEnumerator<int> IEnumerable<int>.GetEnumerator() => Enumerable.Range(0, ++A).GetEnumerator();
    IEnumerator IEnumerable.GetEnumerator() => null;
}
class Program
{
    static void Walk(in S s) { foreach (var x in s) { } }
    static void Generic<T>(in T t) where T : I => t.Bump();
    static void Main()
    {
        var s = new S();
        Walk(in s);
        Generic(in s);
        Console.WriteLine(s.A);
    }
}
"#,
        "0\n",
    );
}

#[test]
fn a_ref_reassignment_is_the_variable_it_points_at() {
    check(
        "RefReassignmentIsVariable",
        r#"
using System;
struct S
{
    public int X;
    public void AddOne() => X++;
}
class Enumerable
{
    readonly int[] items = new int[3];
    public Enumerator GetEnumerator() => new Enumerator(items);
    public struct Enumerator
    {
        readonly int[] items;
        int at;
        public Enumerator(int[] items) { this.items = items; at = -1; }
        public ref int Current => ref items[at];
        public bool MoveNext() => ++at != items.Length;
    }
}
class C
{
    static void M(ref int p) => p++;
    static void Main()
    {
        int a = 0, b = 2;
        ref int r1 = ref a;
        ref int r2 = ref a;
        M(ref r1 = ref r2 = ref b);
        (r1 = ref r2 = ref a) = 7;
        Console.Write(a + " " + b + " ");
        S s1 = new S(), s2 = new S();
        ref S rs = ref s1;
        (rs = ref s2).AddOne();
        (rs = ref s2).X++;
        ref readonly S ro = ref s1;
        (ro = ref s2).AddOne();
        ro.AddOne();
        Console.Write(s1.X + " " + s2.X + " ");
        var e = new Enumerable();
        foreach (ref var x in e) x += 2;
        foreach (ref readonly var x in e) Console.Write(x);
        Console.WriteLine();
    }
}
"#,
        "7 3 0 2 222\n",
    );
}

#[test]
fn a_ref_returning_property_is_called_on_in_place() {
    check(
        "RefPropertyReceiver",
        r#"
using System.Diagnostics.CodeAnalysis;
class C
{
    S1 s1;
    public ref int Value() => ref s1.S2.Value;
    static void Main()
    {
        var c = new C();
        c.Value() = 12;
        var r = new R();
        r.Inner.Bump();
        System.Console.WriteLine(c.Value() + " " + r.Inner.X);
    }
}
struct S1
{
    S2 s2;
    [UnscopedRef] public ref S2 S2 => ref s2;
}
struct S2
{
    int value;
    [UnscopedRef] public ref int Value => ref value;
}
struct Counter
{
    public int X;
    public void Bump() => X++;
}
class R
{
    Counter inner;
    public ref readonly Counter Inner => ref inner;
}
"#,
        "12 0\n",
    );
}

#[test]
fn an_unscoped_ref_parameter_gets_a_delegate_type_of_its_own() {
    check(
        "UnscopedRefDelegate",
        r#"
using System;
using System.Diagnostics.CodeAnalysis;
static class C
{
    static void M([UnscopedRef] ref int x) { }
    static void N(ref int x) { }
    static void Main()
    {
        Delegate m = M, n = N;
        Console.WriteLine(m.GetType() + " " + n.GetType());
    }
}
"#,
        "<>f__AnonymousDelegate0 <>A{00000001}`1[System.Int32]\n",
    );
}

#[test]
fn a_ref_struct_is_a_type_argument_where_allows_ref_struct_says_so() {
    check(
        "AllowsRefStruct",
        r#"
using System;
using System.Collections;
interface I1 { }
ref struct S : IEnumerable, I1
{
    public IEnumerator GetEnumerator() => new[] { 1, 2 }.GetEnumerator();
}
ref struct E : IEnumerator
{
    int at;
    public object Current => at;
    public bool MoveNext() => ++at < 3;
    public void Reset() { }
}
struct Maker { public E Make() => new E(); }
class C
{
    static void Walk<T>(T t) where T : IEnumerable, allows ref struct
    {
        foreach (var x in t) Console.Write(x);
    }
    static void Enumerate<T>(T e) where T : IEnumerator, allows ref struct
    {
        while (e.MoveNext()) Console.Write(e.Current);
    }
    static void Null<T>(T t) where T : allows ref struct => Console.Write(t == null ? "n" : "v");
    static void Same<T>(T t) where T : struct, allows ref struct => Console.Write(t is T);
    static void Main()
    {
        Walk(new S());
        Enumerate(new Maker().Make());
        Null(new S());
        Null<string>(null);
        Same(new S());
        S s = new S();
        Console.Write(s is I1);
        var lambda = (S value) => 1;
        Console.WriteLine(" " + lambda(new S()));
    }
}
"#,
        "1212vnTrueFalse 1\n",
    );
}

#[test]
fn a_ref_parameter_marked_is_read_only_is_an_in_parameter() {
    // No `In` flag and no modifier: only the attribute says `in`, and a
    // value argument reaches it without a `ref`.
    check_with_il_library(
        "IsReadOnlyParameter",
        r#"
.class public abstract auto ansi sealed beforefieldinit Extensions extends [mscorlib]System.Object
{
    .custom instance void [mscorlib]System.Runtime.CompilerServices.ExtensionAttribute::.ctor() = (01 00 00 00)
    .method public hidebysig static void PrintValue(int32& p) cil managed
    {
        .custom instance void [mscorlib]System.Runtime.CompilerServices.ExtensionAttribute::.ctor() = (01 00 00 00)
        .param [1]
        .custom instance void [mscorlib]System.Runtime.CompilerServices.IsReadOnlyAttribute::.ctor() = (01 00 00 00)
        ldarg.0 ldind.i4 call void [mscorlib]System.Console::Write(int32) ret
    }
}
"#,
        r#"
class Program
{
    static void Main()
    {
        int x = 5;
        x.PrintValue();
        Extensions.PrintValue(x);
        Extensions.PrintValue(7);
        System.Console.WriteLine();
    }
}
"#,
        "557\n",
    );
}

#[test]
fn an_implicit_implementation_under_another_in_attribute_is_forwarded_to() {
    // The interface's `ref readonly` return and `in` parameter name the
    // library's `InAttribute`, the class's its own: the runtime matches
    // neither, and a private method with the interface's signature does.
    check_with_library(
        "ForwardedInAttribute",
        r#"
namespace System.Runtime.InteropServices
{
    public class InAttribute {}
}
public interface Parent
{
    ref readonly int M();
    int N(in int x);
}
"#,
        r#"
namespace System.Runtime.InteropServices
{
    public class InAttribute {}
}
public class Child : Parent
{
    private int value = 5;
    public virtual ref readonly int M() => ref value;
    public int N(in int x) => x + 1;
}
public class Program
{
    public static void Main()
    {
        Parent parent = new Child();
        System.Console.WriteLine(parent.M() + " " + parent.N(1));
    }
}
"#,
        "5 2\n",
    );
}

#[test]
fn a_method_group_reaches_a_delegate_through_ref_readonly_and_extensions() {
    check(
        "RefReadonlyMethodGroups",
        r#"
class C
{
    void M(ref int x) => System.Console.Write("C");
    static void In(in int x) => System.Console.Write("I" + x);
    void Run()
    {
        D1 m1 = this.M;
        D2 m2 = this.M;
        D1 m3 = In;
        var i = 1;
        m1(ref i);
        m2(in i);
        m3(ref i);
        System.Console.WriteLine();
    }
    static void Main() => new C().Run();
}
static class E
{
    public static void M(this C c, ref readonly int x) => System.Console.Write("E");
}
delegate void D1(ref int x);
delegate void D2(ref readonly int x);
"#,
        "CEI1\n",
    );
}

#[test]
fn a_union_converts_from_its_cases_and_is_matched_by_what_it_holds() {
    check(
        "unions",
        r#"
[System.Runtime.CompilerServices.Union]
struct Pet
{
    private readonly object _value;
    public Pet(int x) { System.Console.Write("int;"); _value = x; }
    public Pet(string x) { System.Console.Write("string;"); _value = x; }
    public object Value => _value;
    public bool TryGetValue(out int x) { System.Console.Write("try;"); if (_value is int v) { x = v; return true; } x = 0; return false; }
    public static explicit operator Pet(long x) { System.Console.Write("op;"); return new Pet("long"); }
}
[System.Runtime.CompilerServices.Union]
class Boxed : Boxed.IUnionMembers
{
    private readonly object _value;
    private Boxed(object value) { _value = value; }
    object IUnionMembers.Value => _value;
    bool IUnionMembers.HasValue => _value != null;
    public interface IUnionMembers
    {
        public static Boxed Create(int x) => new Boxed(x);
        public static Boxed Create(string x) => new Boxed(x);
        public object Value { get; }
        public bool HasValue { get; }
    }
}
class Program
{
    static string Describe(Pet p) => p switch { int n and > 5 => "big " + n, int => "small", string s => "text " + s, null => "none" };
    static int Label(Pet p)
    {
        switch (p)
        {
            case null: return 0;
            case 1: goto case 2;
            case 2: return 2;
            case "a": return 3;
        }
        return -1;
    }
    static void Main()
    {
        Pet a = 10;
        Pet b = "x";
        Pet c = default;
        Pet d = null;
        Pet e = (Pet)3L;
        System.Console.WriteLine();
        System.Console.WriteLine(Describe(a) + "|" + Describe(b) + "|" + Describe(c) + "|" + Describe(d) + "|" + Describe(e));
        System.Console.WriteLine(a is int && !(b is int) && c is null && d is not null);
        System.Console.WriteLine(Label(1) + " " + Label("a") + " " + Label(default));
        object o = a;
        System.Console.WriteLine(o is Pet and int and 10);
        Boxed x = 5, y = "s";
        Boxed z = null;
        System.Console.WriteLine((x is 5) + " " + (y is string) + " " + (z is null) + " " + (x is null));
    }
}
namespace System.Runtime.CompilerServices { public class UnionAttribute : System.Attribute { } }
"#,
        "int;string;string;op;string;\ntry;try;try;try;try;try;try;try;try;big 10|text x|none|none|text long\ntry;try;False\nint;try;string;try;try;2 3 0\ntry;True\nTrue True True False\n",
    );
}

#[test]
fn an_anonymous_object_is_copied_by_with_and_a_static_extension_is_reached_through_a_derived_type()
{
    check(
        "anonymous_with",
        r#"
using System;
static class E
{
    extension(object)
    {
        public static void M() { Console.Write("M "); }
        public static Action D => () => Console.Write("D ");
    }
}
class C
{
    static T Identity<T>(T t) { Console.Write("[" + t + "]"); return t; }
    static void Main()
    {
        var a = new { A = 10, B = "b", C = 3.5 };
        var b = Identity(a) with { C = Identity(1.5), A = Identity(20) };
        Console.WriteLine(b);
        string.M();
        object.D();
        Console.WriteLine();
    }
}
"#,
        "[{ A = 10, B = b, C = 3.5 }][1.5][20]{ A = 20, B = b, C = 1.5 }\nM D \n",
    );
}

#[test]
fn labeled_break_and_continue_against_the_real_framework() {
    check(
        "LabeledJumps",
        r#"
using System;
using System.Threading.Tasks;

class Program
{
    static async Task<int> Walk()
    {
        int seen = 0;
        outer: for (int i = 0; i < 4; i++)
        {
            for (int j = 0; j < 4; j++)
            {
                try
                {
                    await Task.Yield();
                    if (j == 1) continue outer;
                    if (i == 3) break outer;
                    seen++;
                }
                finally
                {
                    seen += 100;
                }
            }
        }
        return seen;
    }

    static void Main()
    {
        outer: for (int i = 0; i < 3; i++)
        {
            foreach (var c in "abc")
            {
                switch (c)
                {
                    case 'b':
                        continue outer;
                    default:
                        if (i == 2) break outer;
                        break;
                }
                Console.Write($"{i}{c} ");
            }
        }
        Console.WriteLine();
        int n = 0;
        found: while (true)
        {
            n++;
            sw: switch (n % 3)
            {
                case 0:
                    try { break found; } finally { Console.Write("F"); }
                default:
                    break sw;
            }
        }
        Console.WriteLine(n);
        Console.WriteLine(Walk().Result);
    }
}
"#,
        "0a 1a \nF3\n703\n",
    );
}

#[test]
fn an_in_argument_before_an_await_is_handed_over_as_its_value() {
    check(
        "InBeforeAwait",
        r#"
using System.Threading.Tasks;

class Program
{
    static void Main() { Test().Wait(); }

    static async Task Test()
    {
        int local = 1;
        M1(arg3: 3, arg1: RefReturning(ref local), arg2: await GetT(2));
    }

    static ref int RefReturning(ref int arg) => ref arg;

    static async Task<T> GetT<T>(T val)
    {
        await Task.Yield();
        return val;
    }

    static void M1(in int arg1, in int arg2, in int arg3) => System.Console.WriteLine(arg1 + arg2 + arg3);
}
"#,
        "6\n",
    );
}

#[test]
fn goto_case_in_a_switch_over_object_names_the_label_of_its_own_type() {
    check(
        "GotoCaseByType",
        r#"
class Program
{
    static void Main()
    {
        int count = 0;
        switch ((object)(byte)2)
        {
            case (short)2:
                break;
            case (byte)2:
                System.Console.Write("byte ");
                if (++count == 3) break;
                goto case (byte)2;
        }
        switch ((object)(uint)2)
        {
            case (int)2:
                break;
            case (uint)2:
                System.Console.Write("uint ");
                if (++count == 5) break;
                goto case (uint)2;
        }
        long l = 2;
        switch (l)
        {
            case 1: System.Console.Write("one"); break;
            case 2:
                System.Console.Write("long ");
                if (++count == 7) break;
                goto case 1;
        }
    }
}
"#,
        "byte byte byte uint uint long one",
    );
}

#[test]
fn a_checked_context_calls_the_checked_operator_and_nothing_else_does() {
    check(
        "CheckedOperators",
        r#"
using System;

public struct N
{
    public int V;
    public N(int v) { V = v; }
    public static N operator checked +(N a, N b) { Console.Write("checked+ "); return new N(a.V + b.V); }
    public static N operator +(N a, N b) { Console.Write("+ "); return new N(a.V + b.V); }
    public static N operator checked -(N a) { Console.Write("checked- "); return new N(-a.V); }
    public static N operator -(N a) { Console.Write("- "); return new N(-a.V); }
    public static N operator checked ++(N a) { Console.Write("checked++ "); return new N(a.V + 1); }
    public static N operator ++(N a) { Console.Write("++ "); return new N(a.V + 1); }
    public static explicit operator checked int(N a) { Console.Write("checked(int) "); return a.V; }
    public static explicit operator int(N a) { Console.Write("(int) "); return a.V; }
    public static N operator *(N a, N b) { Console.Write("* "); return new N(a.V * b.V); }
}

class Program
{
    static void Main()
    {
        var n = new N(2);
        checked
        {
            n = n + n;
            n = -n;
            n++;
            n = n * n;
            Console.Write((int)n + " ");
            n += n;
        }
        Console.WriteLine();
        n = n + n;
        n = -n;
        n++;
        Console.Write((int)n + " ");
        Console.WriteLine(unchecked((int)checked(n + n)));
        dynamic d = n;
        Console.WriteLine(checked((int)(d + d)));
    }
}
"#,
        "checked+ checked- checked++ * checked(int) 9 checked+ \n+ - ++ (int) -35 checked+ (int) -70\n+ (int) -70\n",
    );
}

#[test]
fn an_interpolated_string_reads_its_text_as_the_string_it_stands_for() {
    check(
        "InterpolatedText",
        r#"
using System;

int x = 5;
Console.WriteLine($"a\tb{x}cA");
Console.WriteLine($@"q""{{{x}}}""");
Console.WriteLine($"{x,4}|{x,-3}|{x:X2}|{1.5:F2}");
Console.WriteLine($"""
    raw {x}
      indented
    """);
Console.WriteLine($$"""{{{x}}} and {not}""");
"#,
        "a\tb5cA\nq\"{5}\"\n   5|5  |05|1.50\nraw 5\n  indented\n{5} and {not}\n",
    );
}

#[test]
fn a_conditional_call_is_kept_where_its_symbol_is_defined_at_the_call() {
    check(
        "ConditionalDefines",
        r#"#define A
#define B
#undef B
using System;
using System.Diagnostics;

class Program
{
    [Conditional("A")] static void a() => Console.Write("a ");
    [Conditional("B")] static void b() => Console.Write("b ");
    [Conditional("C"), Conditional("A")] static void c() => Console.Write("c ");
    static void Main()
    {
        a();
        b();
        c();
    }
}
"#,
        "a c ",
    );
}

#[test]
fn a_string_interpolation_is_built_with_the_default_handler() {
    // `DefaultInterpolatedStringHandler` appends each hole as it comes, so a
    // hole's `ToString` runs after the holes before it are evaluated and
    // before the ones after it, where `string.Format` would evaluate them
    // all first; an addition of interpolated strings is one handler.
    check(
        "DefaultHandler",
        r#"
using System;

class Loud
{
    public string Name;
    public override string ToString() { Console.Write($"[{Name}]"); return Name; }
}

class Program
{
    static Loud Make(string name) { Console.Write("(" + name + ")"); return new Loud { Name = name }; }

    static void Main()
    {
        Console.WriteLine($"{Make("a")}{Make("b")}{Make("c")}");
        Console.WriteLine($"{Make("d")}" + $"-{Make("e")}");
        string s = null;
        Console.WriteLine($"{s}|" + $"{s}");
    }
}
"#,
        "(a)[a](b)[b](c)[c]abc\n(d)[d](e)[e]d-e\n|\n",
    );
}

#[test]
fn caller_member_name_says_the_member_a_caller_is_known_by() {
    check(
        "CallerMemberNames",
        r#"
using System;
using System.Runtime.CompilerServices;

interface I { void Add(); int this[int i] { get; } }

class A { public A([CallerLineNumber] int line = -1) => Console.Write(line + " "); }
class B : A { }

class C : I
{
    void I.Add() => Log();
    int I.this[int i] => Log();
    [IndexerName("Cell")]
    public int this[string s] => Log();
    public int this[long l] => Log();
    public void Outer()
    {
        void Local() => Log();
        Local();
    }
    static int Log([CallerMemberName] string name = "")
    {
        Console.Write(name + " ");
        return 0;
    }
}

class Program
{
    static void Main()
    {
        new B();
        var c = new C();
        ((I)c).Add();
        _ = ((I)c)[0];
        _ = c["x"];
        c.Outer();
    }
}
"#,
        "-1 Add I.Item Cell Outer ",
    );
}

#[test]
fn a_list_pattern_reads_through_an_index_indexer_and_cuts_its_slice() {
    check(
        "ListSlices",
        r#"
using System;

class C
{
    public int Count => 3;
    public int this[Index i] { get { Console.Write("I "); return i.IsFromEnd ? 30 - i.Value : i.Value; } }
    public int this[Range r] { get { Console.Write("R "); return 7; } }
}

class S
{
    public int Length { get { Console.Write("L "); return 4; } }
    public int this[int i] => i * 10;
    public int[] Slice(int start, int length) { Console.Write($"S{start},{length} "); return new int[length]; }
}

class Program
{
    static void Main()
    {
        if (new[] { 4, 2, 0, 0, 0 } is [.. var x, _, _, _]) Console.Write(x.Length + " ");
        if ("0420" is [_, .. var s, _]) Console.Write(s + " ");
        if (new C() is [var a, .. var b, var c]) Console.Write((a, b, c) + " ");
        if (new S() is [0, .. { Length: 2 } m, 30]) Console.Write("m ");
        Console.WriteLine(new S() is [..]);
    }
}
"#,
        "2 42 I R I (0, 7, 29) L S1,2 m True\n",
    );
}

#[test]
fn a_span_of_chars_matches_a_constant_string_by_its_characters() {
    check(
        "SpanStrings",
        r#"
using System;

class Program
{
    const string K = "k";
    static int F(ReadOnlySpan<char> s) => s switch { "" => 0, "ab" => 1, ['a', ..] => 2, _ => 3 };
    static bool G(Span<char> s) => s is (true ? "x" : "y");
    static bool H(Span<char> s) => s is $"{K}!";
    static void Main()
    {
        Console.WriteLine($"{F("")}{F("ab")}{F("ac")}{F("b")} {G("x".ToCharArray())} {H("k!".ToCharArray())}");
    }
}
"#,
        "0123 True True\n",
    );
}

#[test]
fn a_sum_of_utf8_literals_is_one_literal() {
    check(
        "Utf8Sums",
        r#"
using System;

class Program
{
    static ReadOnlySpan<byte> Joined() => "1"u8 + "2"u8 + ("3"u8 + "4"u8);
    static void Main()
    {
        foreach (var b in Joined()) Console.Write(b - '0');
        Console.WriteLine(Joined().Length);
    }
}
"#,
        "12344\n",
    );
}

#[test]
fn a_positional_record_overrides_an_abstract_property_it_inherits() {
    check(
        "RecordAbstractOverride",
        r#"
abstract record A(object X, object Y)
{
    public abstract object X { get; }
    public abstract object Y { get; init; }
}
record B(object X, object Y) : A(X, Y)
{
    public override object X { get; } = X;
}
class Program
{
    static void Main()
    {
        A a = new B(1, 2);
        var (x, y) = a;
        System.Console.WriteLine((a.X, a.Y, x, y));
    }
}
"#,
        "(1, 2, 1, 2)\n",
    );
}

#[test]
fn a_record_prints_its_members_as_roslyn_declares_and_reads_them() {
    check(
        "RecordPrinting",
        r#"
partial record P
{
    public int Y = 22;
}
partial record P(int X)
{
    public int U = 44;
}
record G<T1, T2>(T1 A, T2 B);
record R(in int V)
{
    private int stored = 7;
    public ref int Field => ref stored;
}
record Sealed
{
    public sealed override string ToString() => "sealed";
}
record Derived : Sealed;
class Program
{
    static void Main()
    {
        int v = 5;
        System.Console.WriteLine(new P(11));
        System.Console.WriteLine(new G<int, string>(1, null));
        System.Console.WriteLine(new R(in v));
        System.Console.WriteLine(new Derived());
    }
}
"#,
        "P { Y = 22, X = 11, U = 44 }\nG { A = 1, B =  }\nR { V = 5, Field = 7 }\nsealed\n",
    );
}

#[test]
fn a_nullable_decimal_compares_through_the_decimal_operators() {
    check(
        "NullableDecimalCompare",
        r#"
class Program
{
    static void Main()
    {
        decimal? zero = 0m, none = null, one = 1m;
        System.Console.WriteLine($"{zero != 0.0m} {none != 0.0m} {one != 0.0m} {zero == 0m} {zero >= 0m} {none < 1m} {one > zero}");
    }
}
"#,
        "False True True True True False True\n",
    );
}

#[test]
fn an_increment_through_conversions_steps_a_nullable_number() {
    check(
        "IncrementThroughNullable",
        r#"
class C
{
    public readonly int? i;
    public C(int? i) { this.i = i; }
    public static implicit operator int?(C c) => c.i;
    public static implicit operator C(int? s) => new C(s);
    static void Main()
    {
        C x = new C(10), none = new C(null);
        var old = x++;
        ++none;
        System.Console.WriteLine($"{old.i} {x.i} {(++x).i} {none.i is null}");
    }
}
"#,
        "10 11 12 True\n",
    );
}

#[test]
fn a_write_to_a_static_ref_property_goes_through_its_getter() {
    check(
        "StaticRefProperty",
        r#"
class C
{
    static int stored;
    static ref int Z { get { return ref stored; } }
    static void Main()
    {
        int b;
        (Z, b) = (5, 6);
        System.Console.Write(stored + " ");
        Z = 7;
        Z += 1;
        System.Console.WriteLine(stored);
    }
}
"#,
        "5 8\n",
    );
}

#[test]
fn a_null_for_an_attributes_params_parameter_is_no_array() {
    check(
        "AttributeParamsNull",
        r#"
using System;
using System.Reflection;
sealed class MarkAttribute : Attribute
{
    public MarkAttribute(bool a, params object[] b) { B = b; }
    public MarkAttribute(string s, params int[] n) { N = n; }
    public object[] B { get; }
    public int[] N { get; }
}
[Mark(b: null, a: true)] class P1 { }
[Mark(true, null)] class P2 { }
[Mark("x", null)] class P3 { }
[Mark("x")] class P4 { }
[Mark(true, 1, "two")] class P5 { }
class Program
{
    public static void Main()
    {
        Console.Write(typeof(P1).GetCustomAttribute<MarkAttribute>().B == null);
        Console.Write(" " + (typeof(P2).GetCustomAttribute<MarkAttribute>().B == null));
        Console.Write(" " + (typeof(P3).GetCustomAttribute<MarkAttribute>().N == null));
        Console.Write(" " + typeof(P4).GetCustomAttribute<MarkAttribute>().N.Length);
        Console.WriteLine(" " + typeof(P5).GetCustomAttribute<MarkAttribute>().B.Length);
    }
}
"#,
        "True True True 0 2\n",
    );
}

#[test]
fn an_index_or_range_of_nullables_lifts_as_roslyn_lowers_it() {
    check(
        "NullableIndexRange",
        r#"
using System;

struct S
{
    public int count;
    public int Length => 10;
    public int Slice(int start, int length) { count++; return 0; }
}
class C
{
    public int Length => throw null;
    public int this[Index i, int j = 0] => 1;
    public int this[Range r, int j = 0] => 2;
    public int Slice(int i, int j) => throw null;
}
class Program
{
    static S s;
    static string Show(Index? i) => i is { } v ? $"{(v.IsFromEnd ? "^" : "")}{v.Value}" : "null";
    static string Show(Range? r) => r is { } v ? $"{Show(v.Start)}..{Show(v.End)}" : "null";
    static void Main()
    {
        int? two = 2, none = null;
        Index? start = 1, missing = null;
        Console.Write(Show(^two) + " " + Show(^none) + " " + Show(^new int?()) + " ");
        Console.Write(Show(start..^0) + " " + Show(start..missing) + " " + Show(..missing) + " ");
        _ = s[1..2];
        var c = new C();
        Console.WriteLine($"{s.count} {c[^1]} {c[1..]}");
    }
}
"#,
        "^2 null ^0 1..^0 null null 1 1 2\n",
    );
}

#[test]
fn a_decimal_pattern_compares_through_the_decimal_operators() {
    check(
        "DecimalPatterns",
        r#"
class C
{
    static char Grade(decimal score) => score switch { <= 60.000m => 'F', <= 70.00m => 'D', 1000m => 'M', > 90m => 'A', _ => 'x' };
    static string K(object o) => o switch { 1.5m => "half", decimal d when d > 2 => "big", _ => "other" };
    static void Main() => System.Console.WriteLine($"{Grade(50m)}{Grade(65.5m)}{Grade(1000.00m)}{Grade(95m)}{Grade(80m)} {K(1.50m)} {K(3m)} {K(1m)}");
}
"#,
        "FDMAx half big other\n",
    );
}

#[test]
fn a_call_on_an_element_of_a_covariant_t_array_reads_it_readonly() {
    check(
        "ReadonlyElementReceiver",
        r#"
class Moo<T>
{
    public void Goo(T[] x) => System.Console.Write(x[0].ToString() + " ");
}
class Program
{
    static string Hex(decimal d) => string.Join("", System.Array.ConvertAll(decimal.GetBits(d), w => w.ToString("x8")));
    static void Main()
    {
        new Moo<System.Exception>().Goo(new System.ApplicationException[] { new System.ApplicationException("hello") });
        System.Console.WriteLine(Hex(0E-100M));
    }
}
"#,
        "System.ApplicationException: hello 000000000000000000000000001c0000\n",
    );
}

#[test]
fn a_nan_pattern_asks_is_nan() {
    check(
        "NaNPatterns",
        r#"
class Program
{
    static bool P(object o) => o switch { double.NaN => true, float.NaN => true, _ => false };
    static void Main()
    {
        double d = double.NaN;
        float f = float.NaN;
        System.Console.WriteLine($"{d is double.NaN} {1.0 is double.NaN} {f is float.NaN} {P(double.NaN)} {P(float.NaN)} {P(0.0)}");
    }
}
"#,
        "True False True True True False\n",
    );
}

#[test]
fn an_irrefutable_positional_pattern_assigns_and_var_empty_asks_for_an_object() {
    check(
        "IrrefutablePositional",
        r#"
public struct Pair
{
    public int Left, Right;
    public void Deconstruct(out int left, out int right) => (left, right) = (Left, Right);
}
public class C
{
    public void Deconstruct() { }
    static bool Empty(C c) => c is var ();
    public static void Main()
    {
        if (new Pair { Left = 1, Right = 2 } is Pair(int left, var right)) { }
        System.Console.WriteLine($"{left} {right} {Empty(new C())} {Empty(null)}");
    }
}
"#,
        "1 2 True False\n",
    );
}

#[test]
fn an_interpolated_string_handler_is_made_with_the_arguments_its_parameter_names() {
    check(
        "HandlerArguments",
        r#"
using System;
using System.Runtime.CompilerServices;
using System.Text;

class Program
{
    static int Get(int i) { Console.WriteLine("Get" + i); return i; }

    static void Main()
    {
        var c = new C { Name = "c" };
        c.M(Get(1), $"text {Get(2)}");
        c.M(Get(3), $"stop {Get(4)}");
        Console.WriteLine(C.Pick($"{1}"));
        Console.WriteLine(C.Pick($"constant"));
        var s = new S();
        s.Count($"counted");
        Console.WriteLine(s.Calls);
    }
}

public class C
{
    public string Name;
    public void M(int limit, [InterpolatedStringHandlerArgument("", "limit")] Handler h) => Console.WriteLine(h.ToString());
    public static string Pick(string s) => "string";
    public static string Pick(Handler h) => "handler";
}

public struct S
{
    public int Calls;
    public void Count([InterpolatedStringHandlerArgument("")] Handler h) => Calls++;
}

[InterpolatedStringHandler]
public ref struct Handler
{
    private StringBuilder _builder;
    public Handler(int literalLength, int formattedCount) { _builder = new StringBuilder(); }
    public Handler(int literalLength, int formattedCount, S s) { _builder = new StringBuilder(); }
    public Handler(int literalLength, int formattedCount, C c, int limit, out bool proceed)
    {
        _builder = new StringBuilder(c.Name + ":" + literalLength + "," + formattedCount + " ");
        proceed = limit < 3;
    }
    public void AppendLiteral(string s) => _builder.Append(s);
    public void AppendFormatted<T>(T value) => _builder.Append(value);
    public override string ToString() => _builder.ToString();
}
"#,
        "Get1\nGet2\nc:5,1 text 2\nGet3\nc:5,1 \nhandler\nstring\n1\n",
    );
}

#[test]
fn an_unmanaged_constraint_is_a_struct_constraint_in_metadata() {
    check(
        "UnmanagedConstraint",
        r#"
class A<T> where T : struct
{
    public void M(T arg) => System.Console.Write(arg + " ");
}
class B<T> : A<T> where T : unmanaged { }
class Program
{
    static void Main()
    {
        new B<int>().M(5);
        System.Console.WriteLine(typeof(B<>).GetGenericArguments()[0].GenericParameterAttributes);
    }
}
"#,
        "5 NotNullableValueTypeConstraint, DefaultConstructorConstraint\n",
    );
}

#[test]
fn a_coalescing_assignment_tests_a_type_parameter_boxed_and_default_as_the_underlying_type() {
    check(
        "CoalescingAssignmentOfT",
        r#"
using System;
class C
{
    static void Verify<T>(T t1, T t2) { Console.Write(t1 ??= t2); Console.Write(","); Console.Write(t1); Console.Write(" "); }
    static void Main()
    {
        Verify<object>(null, "a");
        Verify<int>(default, 10);
        Verify<int?>(null, 1);
        Verify<int?>(2, 10);
        int? a = null;
        Console.Write(a ??= default);
        Console.WriteLine(a ??= 1);
    }
}
"#,
        "a,a 0,0 1,1 2,2 00\n",
    );
}

#[test]
fn a_ref_getter_is_called_once_by_a_compound_assignment() {
    check(
        "RefGetterOnce",
        r#"
using System;
public class C
{
    int f = 1;
    int? g;
    int[] items = new int[3];
    ref int P { get { Console.Write("P "); return ref f; } }
    ref int? Q { get { Console.Write("Q "); return ref g; } }
    ref int this[int i] { get { Console.Write("this "); return ref items[i]; } }
    public static void Main()
    {
        var c = new C();
        c.P += 5;
        c.P++;
        Console.Write(c.Q ??= 3);
        c[1] += 2;
        Console.WriteLine($"{c.f} {c.g} {c.items[1]}");
    }
}
"#,
        "P P Q 3this 7 3 2\n",
    );
}

#[test]
fn a_coalescing_assignment_of_a_variable_awaits_only_where_it_is_null() {
    check(
        "CoalescingAssignmentAwait",
        r#"
using System;
using System.Threading.Tasks;
class C
{
    static Task<int> Get(int i) { Console.Write("get "); return Task.FromResult(i); }
    static async Task Main()
    {
        int? i = null;
        Console.Write(i ??= await Get(2));
        Console.WriteLine(i ??= await Get(3));
    }
}
"#,
        "get 22\n",
    );
}

#[test]
fn new_on_a_com_import_interface_makes_its_coclass() {
    check(
        "CoClassCreation",
        r#"
using System;
using System.Runtime.InteropServices;
class Worksheet : IWorksheet
{
    int i;
    public Worksheet() { }
    public Worksheet(int i) { this.i = i; }
    public int M1() => i;
}
public class Pair<T, U> : IPair<T>
{
    public Pair(U x) { Console.Write(x + " "); }
}
[ComImport, Guid("00020810-0000-0000-C000-000000000046")]
[CoClass(typeof(Worksheet))]
interface IWorksheet
{
    int M1();
}
[ComImport, Guid("00020810-0000-0000-C000-000000000047")]
[CoClass(typeof(Pair<int, string>))]
public interface IPair<T> { }
class Program
{
    static void Main()
    {
        var a = new IWorksheet();
        IWorksheet b = new IWorksheet(2);
        var c = (Worksheet)new IWorksheet(3);
        var d = new IPair<int>("x");
        Console.WriteLine($"{a.M1()} {b.M1()} {c.M1()} {typeof(IWorksheet).IsImport} {d.GetType().Name}");
    }
}
"#,
        "x 0 2 3 True Pair`2\n",
    );
}

#[test]
fn a_handler_appended_to_across_an_await_is_made_before_it() {
    // The handler and the appends before the hole that waits are done
    // before the `await`, as csc does them, and the handler is kept across
    // it in the machine.
    check(
        "HandlerAcrossAwait",
        r#"
using System;
using System.Runtime.CompilerServices;
using System.Text;
using System.Threading.Tasks;

class Program
{
    static async Task<int> A(int i) { await Task.Yield(); Console.Write("A" + i + " "); return i; }
    static int I(int i) { Console.Write("I" + i + " "); return i; }

    static async Task Run()
    {
        M(I(1), $"x{I(2)}y{await A(3)}z");
        Console.WriteLine();
        Console.WriteLine($"s{I(4)}t{await A(5)}");
    }

    static void M(int n, [InterpolatedStringHandlerArgument("n")] Handler h) => Console.Write("M " + h);

    static void Main() => Run().Wait();
}

[InterpolatedStringHandler]
public struct Handler
{
    private StringBuilder _builder;
    public Handler(int literalLength, int formattedCount, int n) { Console.Write("ctor" + n + " "); _builder = new StringBuilder(); }
    public void AppendLiteral(string s) { Console.Write("L" + s + " "); _builder.Append(s); }
    public void AppendFormatted<T>(T value) { Console.Write("F" + value + " "); _builder.Append(value); }
    public override string ToString() => _builder.ToString();
}
"#,
        "I1 ctor1 Lx I2 F2 Ly A3 F3 Lz M x2y3z\nI4 A5 s4t5\n",
    );
}

#[test]
fn a_switch_with_a_target_typed_new_arm_takes_the_type_of_the_other_arms() {
    check(
        "SwitchNaturalTypeWithNew",
        r#"
using static System.Console;

var c0 = 0 switch { 1 => new C(), int n => new() { n = n + 5 } };
var c1 = 1 switch { 1 => new C { n = 7 }, _ => new() };
WriteLine($"{c0.n} {c1.n} {c0.GetType().Name}");

class C
{
    public int n;
}
"#,
        "5 7 C\n",
    );
}

#[test]
fn caller_info_in_attributes_follows_roslyn() {
    check(
        "CallerInfoInAttributes",
        r#"
using System;
using System.Reflection;
using System.Runtime.CompilerServices;
class Name : Attribute
{
    public Name([CallerMemberName] string name = "<none>") => Console.Write(name + " ");
}
class Line : Attribute
{
    public Line([CallerLineNumber] float line = 0) => Console.Write(line + " ");
}
class Program
{
    const string p = nameof(p);
    [Name] public int field;
    public static void Bar([Name] int x) { }
    public static void Log(int p, [CallerArgumentExpression(p)] string arg = "<d>") => Console.Write(arg + " ");
    static void At([CallerLineNumber] int line = 0) => Console.Write(line + " ");
    [Line]
    static void Main()
    {
        typeof(Program).GetField("field").GetCustomAttribute(typeof(Name));
        typeof(Program).GetMethod("Bar").GetParameters()[0].GetCustomAttribute(typeof(Name));
        typeof(Program).GetMethod("Main", BindingFlags.NonPublic | BindingFlags.Static).GetCustomAttribute(typeof(Line));
        Log(2 + 2);
        At
            (
            );
        Console.WriteLine();
    }
}
"#,
        "<none> Bar 20 2 + 2 28 \n",
    );
}

#[test]
fn attributes_go_on_type_parameters_and_take_named_arguments_in_any_order() {
    check(
        "TypeParameterAttributes",
        r#"
using System;
using System.Reflection;
public class A : Attribute
{
    public A(int x, params object[] rest) => Console.Write(x + ":" + rest.Length + " ");
}
class B
{
    const int X = 1;
    [A(rest: new object[] { "a", "b" }, x: X)]
    class C<[A(X)] T, U>
    {
        const int X = 2;
        public void M<[A(3)] V>() { }
    }
    static void Main()
    {
        typeof(C<,>).GetCustomAttributes(false);
        typeof(C<,>).GetGenericArguments()[0].GetCustomAttributes(false);
        Console.Write(typeof(C<,>).GetGenericArguments()[1].GetCustomAttributes(false).Length + " ");
        typeof(C<,>).GetMethod("M").GetGenericArguments()[0].GetCustomAttributes(false);
        Console.WriteLine();
    }
}
"#,
        "2:2 2:0 0 3:0 \n",
    );
}

#[test]
fn new_t_on_a_struct_parameter_runs_its_parameterless_constructor() {
    check(
        "NewTStruct",
        r#"
using System;
struct S
{
    public bool Initialized;
    public S() { Initialized = true; }
}
partial class C
{
    public void Call()
    {
        int x = 0;
        M(x);
        M(in x);
    }
    partial void M(in int i);
    partial void M(int i);
    partial void M(int i) => Console.Write("none ");
    partial void M(in int i) => Console.Write("in ");
}
class Program
{
    static T CreateStruct<T>() where T : struct => new T();
    static void Main()
    {
        new C().Call();
        Console.WriteLine(CreateStruct<S>().Initialized);
    }
}
"#,
        "none in True\n",
    );
}

#[test]
fn decimal_constants_fold_as_roslyn_folds_them() {
    check(
        "DecimalFolding",
        r#"
using System;
using System.Globalization;
class Program
{
    static bool IsZero(decimal x) => Array.TrueForAll(decimal.GetBits(x), part => part == 0);
    static string Show(double d) => d.ToString(CultureInfo.InvariantCulture);
    static void Main()
    {
        var z = new decimal[] { -(decimal.Zero), -0m };
        Console.Write($"{IsZero(z[0])} {IsZero(z[1])} {IsZero(-0.0m)} ");
        Console.Write(Show(1d / (double)(-0m)) + " " + Show(1d / (double)(1m * -0m)) + " ");
        Console.Write(Show(1d / (double)(-0m + 0m)) + " " + Show(1d / (double)(0m - -0m)) + " ");
        Console.WriteLine((1.5m * 2.0m) + " " + (1.25m + 1m) + " " + (1m - 3.5m));
    }
}
"#,
        "True True False -Infinity -Infinity -Infinity Infinity 3.00 2.25 -2.5\n",
    );
}

#[test]
fn a_user_defined_and_also_in_an_expression_tree_names_its_method() {
    check(
        "TreeAndAlso",
        r#"
using System;
using System.Linq.Expressions;
class C
{
    public static bool operator false(C c) { Console.Write("f "); return false; }
    public static bool operator true(C c) => false;
    public static C operator &(C a, C b) { Console.Write("& "); return a; }
}
class Program
{
    static void Main()
    {
        Expression<Func<C, C, C>> tree = (x, y) => x && y;
        var body = (BinaryExpression)tree.Body;
        Console.Write(body.NodeType + " " + body.Method.Name + " ");
        tree.Compile()(new C(), new C());
        Console.WriteLine();
    }
}
"#,
        "AndAlso op_BitwiseAnd f & \n",
    );
}

#[test]
fn named_indices_checked_pointers_and_dynamic_ref_receivers() {
    check(
        "NamedIndicesPointers",
        r#"
using System;
unsafe class A
{
    A this[int x, int y] { get { Console.Write(x + "," + y + " "); return new A(); } }
    int X;
    static void* ToPointer(nint i) => checked((void*)i);
    static nint FromPointer(void* p) => checked((nint)p);
    static ref S GetS(ref S s) => ref s;
    static void Main()
    {
        int x = 1;
        new A { [y: x++, x: x++] = { X = 1 } };
        try { ToPointer(-42); } catch (OverflowException) { Console.Write("overflow "); }
        try { FromPointer((void*)ulong.MaxValue); } catch (OverflowException) { Console.Write("overflow "); }
        dynamic d = 7;
        S s = default;
        GetS(ref s).M(d);
        Console.WriteLine(s.X);
    }
}
struct S
{
    public int X { get; private set; }
    public void M(int x) => X = x;
}
"#,
        "2,1 overflow overflow 7\n",
    );
}

#[test]
fn a_constant_pattern_narrows_and_a_property_chain_reads_through_a_nullable() {
    check(
        "PatternNarrowing",
        r#"
using System;
struct S1
{
    public S1(object value) => Value = value;
    public object Value { get; }
}
struct S2
{
    public S2(S1? s1) => S1 = s1;
    public S1? S1 { get; }
}
class Program
{
    static bool A(object o) => o is "11" and ['1', '1'];
    static bool B(S2 u) => u is { S1.Value: "11" and [_, '1'] };
    static bool C(S2 u) => u is { S1.Value: 10 };
    static void Main()
    {
        Console.WriteLine($"{A("11")} {A(11)} {B(new S2(new S1("11")))} {B(new S2(null))} {C(new S2(new S1(10)))} {C(new S2(null))}");
    }
}
"#,
        "True False True False True False\n",
    );
}

/// A deconstruction runs in phases across the whole of it, as Roslyn lowers
/// it: the places on the left (receivers, indices, what a `ref`-returning
/// method hands back), then the right and every `Deconstruct`, then every
/// conversion, then every assignment. A tuple literal's elements convert as
/// they are evaluated, a conditional's branches are taken apart one by one,
/// a nested tuple value is read after the literal elements beside it, and a
/// struct is taken apart as a copy. `_ = s` is a value, not the variable.
#[test]
fn a_deconstruction_evaluates_in_phases() {
    check(
        "deconstruction_phases",
        r#"
using System;
class C
{
    public string Name;
    public int X { set => Console.Write(Name + ".X=" + value + " "); }
    public int this[int i] { set => Console.Write(Name + "[" + i + "]=" + value + " "); }
    public C Holder(string name) { Console.Write("holder" + name + " "); return new C { Name = name }; }
    public void Deconstruct(out D a, out D b) { Console.Write("Deconstruct "); a = new D(1); b = new D(2); }
}
class D
{
    int value;
    public D(int value) { Console.Write("new" + value + " "); this.value = value; }
    public static implicit operator int(D d) { Console.Write("convert" + d.value + " "); return d.value; }
}
struct S
{
    public int A;
    public void Deconstruct(out int a, out int b) { a = A; b = 0; A = 100; }
}
class Program
{
    static int[] cells = new int[2];
    static ref int Cell(int i) { Console.Write("cell" + i + " "); return ref cells[i]; }
    static int Log(int v) { Console.Write("log" + v + " "); return v; }
    static (int, int) Pair() { Console.Write("pair "); return (1, 2); }
    static void Main()
    {
        var c = new C { Name = "c" };
        (c.Holder("x").X, c.Holder("y")[Log(0)]) = c;
        Console.WriteLine();
        (c.Holder("x").X, c.Holder("y").X) = (new D(3), new D(4));
        Console.WriteLine();
        bool flag = true;
        (c.Holder("x").X, c.Holder("y").X) = flag ? (new D(5), new D(6)) : default;
        Console.WriteLine();
        (Cell(0), Cell(1)) = (Log(7), Log(8));
        Console.WriteLine(cells[0] + " " + cells[1]);
        int a, b, d;
        ((a, b), d) = (Pair(), Log(3));
        Console.WriteLine(a + " " + b + " " + d);
        (c.X, _) = (Log(9), c = new C { Name = "other" });
        Console.WriteLine();
        var s = new S { A = 1 };
        var (s1, s2) = s;
        Console.WriteLine(s1 + " " + s.A);
        (_ = s).Deconstruct(out _, out _);
        Console.WriteLine(s.A);
    }
}
"#,
        "holderx holdery log0 Deconstruct new1 new2 convert1 convert2 x.X=1 y[0]=2 \n\
         holderx holdery new3 convert3 new4 convert4 x.X=3 y.X=4 \n\
         holderx holdery new5 new6 convert5 convert6 x.X=5 y.X=6 \n\
         cell0 cell1 log7 log8 7 8\n\
         log3 pair 1 2 3\n\
         log9 c.X=9 \n\
         1 1\n\
         1\n",
    );
}

/// A query over a type that is no sequence calls the methods the type
/// declares, generic ones among them, with delegates of its own: each
/// range variable is what the method's delegate is handed — `Join`'s inner
/// one and `SelectMany`'s second inferred from the inner sequence and the
/// first lambda — and each lambda is handed over as that delegate. `group x
/// by k` of the one range variable calls the `GroupBy` of one argument.
#[test]
fn a_query_calls_the_methods_of_a_type_that_is_no_sequence() {
    check(
        "query_pattern_methods",
        r#"
using System;
public delegate R F1<in T, out R>(T a);
public delegate R F2<in T1, in T2, out R>(T1 a, T2 b);
public class Seq<T>
{
    public T[] Items;
    public Seq(params T[] items) { Items = items; }
    public Seq<T> Where(F1<T, bool> p) { var r = new System.Collections.Generic.List<T>(); foreach (var i in Items) if (p(i)) r.Add(i); return new Seq<T>(r.ToArray()); }
    public Seq<U> Select<U>(F1<T, U> f) { var r = new U[Items.Length]; for (int i = 0; i < r.Length; i++) r[i] = f(Items[i]); return new Seq<U>(r); }
    public Seq<V> SelectMany<U, V>(F1<T, Seq<U>> f, F2<T, U, V> g)
    {
        var r = new System.Collections.Generic.List<V>();
        foreach (var t in Items) foreach (var u in f(t).Items) r.Add(g(t, u));
        return new Seq<V>(r.ToArray());
    }
    public Seq<V> Join<U, K, V>(Seq<U> inner, F1<T, K> outerKey, F1<U, K> innerKey, F2<T, U, V> result)
    {
        var r = new System.Collections.Generic.List<V>();
        foreach (var t in Items) foreach (var u in inner.Items) if (outerKey(t).Equals(innerKey(u))) r.Add(result(t, u));
        return new Seq<V>(r.ToArray());
    }
    public Seq<V> GroupJoin<U, K, V>(Seq<U> inner, F1<T, K> outerKey, F1<U, K> innerKey, F2<T, Seq<U>, V> result)
    {
        var r = new V[Items.Length];
        for (int i = 0; i < r.Length; i++) r[i] = result(Items[i], inner.Where(u => innerKey(u).Equals(outerKey(Items[i]))));
        return new Seq<V>(r);
    }
    public Seq<T> OrderByDescending<K>(F1<T, K> key) { var r = (T[])Items.Clone(); Array.Sort(r, (a, b) => Comparer(key(b), key(a))); return new Seq<T>(r); }
    static int Comparer<K>(K a, K b) => System.Collections.Generic.Comparer<K>.Default.Compare(a, b);
    public Seq<string> GroupBy<K>(F1<T, K> key) { Console.Write("GroupBy1 "); return Select(t => key(t) + "=" + t); }
    public Seq<string> GroupBy<K, E>(F1<T, K> key, F1<T, E> element) { Console.Write("GroupBy2 "); return Select(t => key(t) + "=" + element(t)); }
    public Seq<E> Cast<E>() => Select(t => (E)(object)t);
    public override string ToString() => "[" + string.Join(", ", Items) + "]";
}
class Program
{
    static void Main()
    {
        var xs = new Seq<int>(1, 2, 3);
        var ys = new Seq<int>(10, 20, 30);
        Console.WriteLine(from x in xs where x > 1 select x * 2);
        Console.WriteLine(from x in xs from y in ys select x + y);
        Console.WriteLine(from x in xs join y in ys on x equals y / 10 select x + ":" + y);
        Console.WriteLine(from x in xs join y in ys on x equals y / 20 into g select x + ":" + g);
        Console.WriteLine(from x in xs let z = x * x orderby z descending select z);
        Console.WriteLine(from x in xs group x by x % 2);
        Console.WriteLine(from x in xs group x * 10 by x % 2);
        Console.WriteLine(from object o in new Seq<object>(4, 5) select (int)o + 1);
        Console.WriteLine(from x in xs select x into y where y != 2 select y);
    }
}
"#,
        "[4, 6]\n\
         [11, 21, 31, 12, 22, 32, 13, 23, 33]\n\
         [1:10, 2:20, 3:30]\n\
         [1:[20, 30], 2:[], 3:[]]\n\
         [9, 4, 1]\n\
         GroupBy1 [1=1, 0=2, 1=3]\n\
         GroupBy2 [1=10, 0=20, 1=30]\n\
         [5, 6]\n\
         [1, 3]\n",
    );
}

/// An iterator's machine keeps its locals in the fields `csc` does, named as
/// it names them: in an optimized build only the locals a `yield` comes
/// between the write and the read of, numbered from `5__2` as their scopes
/// are entered, a later local of the same type taking the field of one whose
/// scope has ended (the `foreach`'s array and index are `<>7__wrapN`); in a
/// debug build every local, in fields of their own numbered from `5__1`. The
/// fields are private but for `<>3__p`, which the method making the machine
/// fills and `GetEnumerator` copies into `p`, and a local that might hold a
/// reference is cleared where its scope ends.
#[test]
fn an_iterator_keeps_its_locals_in_the_fields_csc_does() {
    let source = r#"
using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;

class C
{
    static IEnumerable<int> Produce(int p)
    {
        int unused = p + 1;
        Console.Write(unused + " ");
        {
            string s = "first";
            yield return 1;
            Console.Write(s + " ");
        }
        {
            string t = "second";
            yield return 2;
            Console.Write(t + " ");
        }
        foreach (var e in new[] { 3 })
        {
            yield return e;
        }
    }

    static string Fields(object machine) =>
        string.Join(" ", machine.GetType().GetFields(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance)
            .Where(f => f.Name != "<>w__disposing")
            .Select(f => f.Name + (f.IsPublic ? "+" : "-"))
            .OrderBy(n => n, StringComparer.Ordinal));

    static void Main()
    {
        var values = Produce(5);
        Console.WriteLine(Fields(values));
        var e = values.GetEnumerator();
        var field = e.GetType().GetFields(BindingFlags.NonPublic | BindingFlags.Instance).First(f => f.Name.StartsWith("<s>"));
        while (e.MoveNext())
            Console.WriteLine(e.Current + ": " + (field.GetValue(e) ?? "null"));
    }
}
"#;
    use rustlyn_syntax::LanguageVersion;
    let optimized = rustlyn_semantics::CompilationOptions {
        optimize: true,
        ..Default::default()
    };
    check_with_options(
        "IteratorFieldsOptimized",
        LanguageVersion::CSharp11,
        optimized,
        source,
        "<>1__state- <>2__current- <>3__p+ <>7__wrap2- <>7__wrap3- <>l__initialThreadId- <s>5__2- p-\n\
         6 1: first\n\
         first 2: second\n\
         second 3: null\n",
    );
    check_with_options(
        "IteratorFieldsDebug",
        LanguageVersion::CSharp11,
        rustlyn_semantics::CompilationOptions::default(),
        source,
        "<>1__state- <>2__current- <>3__p+ <>l__initialThreadId- <>s__4- <>s__5- <e>5__6- <s>5__2- <t>5__3- <unused>5__1- p-\n\
         6 1: first\n\
         first 2: null\n\
         second 3: null\n",
    );
}

/// A method ending in `__arglist` is called another way than one without,
/// so the two are no duplicates of each other, and a deconstruction, which
/// passes no `__arglist`, takes the one without it.
#[test]
fn a_varargs_deconstruct_is_no_duplicate_and_no_deconstruct() {
    check(
        "VarargsDeconstruct",
        r#"
class C
{
    static void Main()
    {
        long x;
        string y;
        (x, y) = new C();
        System.Console.WriteLine(x + " " + y);
    }
    public void Deconstruct(out int a, out string b) { a = 1; b = "hello"; }
    public void Deconstruct(out int a, out string b, __arglist) { a = 2; b = "ignored"; }
}
"#,
        "1 hello\n",
    );
}

/// A `foreach` inside an iterator keeps its enumerator in a field of the
/// machine, since a `yield` comes between its uses, and the `finally` that
/// disposes it reads it from there: the inner loop's enumerator is disposed
/// as it ends, the outer one's as the exception leaves it.
#[test]
fn an_iterator_disposes_the_enumerators_it_keeps_in_fields() {
    check(
        "IteratorForEachDispose",
        r#"
using System;
using System.Collections;
using System.Collections.Generic;
class Seq : IEnumerable<int>
{
    string name;
    public Seq(string name) { this.name = name; }
    public IEnumerator<int> GetEnumerator() => new En(name);
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
    class En : IEnumerator<int>
    {
        string name; int at = -1;
        public En(string name) { this.name = name; }
        public int Current => at;
        object IEnumerator.Current => at;
        public bool MoveNext() => ++at < 1;
        public void Reset() { }
        public void Dispose() => Console.Write("dispose" + name + " ");
    }
}
class Program
{
    static IEnumerable<int> Walk()
    {
        foreach (var i in new Seq("Outer"))
        {
            foreach (var j in new Seq("Inner"))
            {
                yield return i + j;
            }
            throw new Exception("thrown");
        }
    }
    static void Main()
    {
        try
        {
            foreach (var value in Walk()) Console.Write(value + " ");
        }
        catch (Exception e)
        {
            Console.WriteLine(e.Message);
        }
    }
}
"#,
        "0 disposeInner disposeOuter thrown\n",
    );
}

#[test]
fn a_positional_pattern_matches_through_ituple_and_a_record_keeps_its_deconstruct() {
    check(
        "ITuplePatterns",
        r#"
using System;
using System.Runtime.CompilerServices;
class Q : ITuple
{
    public int Length => 2;
    public object this[int index] => index + 3;
}
record B(int X)
{
    public void Deconstruct(int X) { }
}
class Program
{
    static void M<T>(T t) => Console.Write(typeof(T).Name + " ");
    static void Main()
    {
        object o = new Q();
        Console.Write($"{o is (3, 4)} {o is (3, 5)} {o is (3, 4, 5)} ");
        if (o is (3, 4) and var i) M(i);
        o = 1u;
        if (o is <= 10U and var u) M(u);
        o = 1;
        if (o is (1 or 2) and var n) M(n);
        long x = 42;
        if (x is 42 and var l) M(l);
        if (new B(7) is B(int y)) Console.Write(y);
        Console.WriteLine();
    }
}
"#,
        "True False False ITuple UInt32 Int32 Int64 7\n",
    );
}

#[test]
fn a_type_in_an_attribute_names_its_assembly_and_int_is_the_core_librarys() {
    check(
        "AttributeTypeNames",
        r#"
using System;
using System.Collections.Generic;
namespace System
{
    class Int32 { }
}
[A(Type = typeof(int*), Other = typeof(List<int>))]
class A : Attribute
{
    public Type Type, Other;
    static void Main()
    {
        var a = (A)typeof(A).GetCustomAttributes(false)[0];
        Console.WriteLine($"{a.Type == typeof(int*)} {a.Other == typeof(List<int>)} {typeof(A).GetCustomAttributesData().Count}");
    }
}
"#,
        "True True 1\n",
    );
}

#[test]
fn dynamic_conditions_and_user_defined_logic_on_nullables() {
    check(
        "DynamicConditions",
        r#"
using System;
public struct S1
{
    public static S1 operator &(S1 x, S1 y) { Console.Write("& "); return x; }
    public static bool operator false(S1? x) { Console.Write("false "); return false; }
    public static bool operator true(S1? x) { Console.Write("true "); return true; }
}
class Counter
{
    int i;
    public bool More { get { return i < 2; } }
    public void Next() => i++;
}
class Program
{
    static S1? And(S1? s) => s && s;
    static void Main()
    {
        dynamic d = new Counter();
        int n = 0;
        for (; d.More; d.Next()) n++;
        dynamic yes = true;
        var arm = 1 switch { _ when yes => "when", _ => "no" };
        And(new S1());
        S1? s = new S1();
        if (s) Console.Write("if ");
        Console.WriteLine($"{n} {arm}");
    }
}
"#,
        "false & true if 2 when\n",
    );
}

#[test]
fn delegates_combine_with_plus_and_nulls_compare_as_int_nullables() {
    check(
        "DelegatePlus",
        r#"
using System;
class C
{
    delegate void D();
    static void A() => Console.Write("a ");
    static void B() => Console.Write("b ");
    static void Main()
    {
        D a = A, b = B;
        D both = a + b;
        both();
        (both - a)();
        Console.WriteLine($"{both - a == b} {null > null} {null <= null}");
    }
}
"#,
        "a b b True False False\n",
    );
}

#[test]
fn a_null_operand_takes_the_type_the_declared_operator_wants() {
    check(
        "NullOperand",
        r#"
using System;
struct SX
{
    public static SZ operator *(SX x, SY y) => new SZ();
}
struct SY { }
struct SZ { }
class Program
{
    static void Main()
    {
        SX sx = new SX();
        SX? sxn = null;
        Console.WriteLine($"{(sx * null).HasValue} {(sxn * new SY()).HasValue} {(sx * new SY?(new SY())).HasValue}");
    }
}
"#,
        "False False True\n",
    );
}

#[test]
fn fixed_void_pointers_and_a_stackalloc_into_a_readonly_span() {
    check(
        "FixedVoid",
        r#"
using System;
unsafe class C
{
    char c = 'a';
    char[] a = new char[] { 'b' };
    static void Main()
    {
        C c = new C();
        fixed (void* p = &c.c, q = c.a, r = "hello")
        {
            Console.Write((int)*(char*)p + " " + (int)*(char*)q + " " + (int)*(char*)r + " ");
        }
        ReadOnlySpan<int> span = stackalloc int[3] { 1, 2, 3 };
        Console.WriteLine(span[0] + span[1] + span[2]);
    }
}
"#,
        "97 98 104 6\n",
    );
}

#[test]
fn an_indexer_name_is_written_as_its_attribute_says() {
    check(
        "IndexerNames",
        r#"
using System;
using System.Linq;
using System.Reflection;
class C
{
    public int Other(int index) => 0;
    [System.Runtime.CompilerServices.IndexerName("_" + nameof(Other))]
    public int this[int index] => index * 2;
}
class D
{
    [System.Runtime.CompilerServices.IndexerName("Chars")]
    public char this[int index] => 'x';
}
class Program
{
    static void Main()
    {
        var names = typeof(C).GetMethods().Where(m => m.DeclaringType == typeof(C)).Select(m => m.Name).OrderBy(n => n);
        Console.WriteLine(string.Join(" ", names) + " " + typeof(D).GetCustomAttribute<DefaultMemberAttribute>().MemberName + " " + new C()[21] + new D()[0]);
    }
}
"#,
        "get__Other Other Chars 42x\n",
    );
}

#[test]
fn a_cast_is_a_copy_and_a_slice_is_taken_to_be_something() {
    check(
        "CastCopy",
        r#"
class C
{
    public int Length => 3;
    public int this[int i] => 0;
    public int[] Slice(int i, int j) => null;
}
class Program
{
    struct S1
    {
        public int field;
        public int Increment() => field++;
    }
    static void Main()
    {
        S1 v = default(S1);
        v.Increment();
        ((S1)v).Increment();
        System.Console.WriteLine($"{v.field} {new C() is [.. {}]} {new C() is [.. null]}");
    }
}
"#,
        "1 True True\n",
    );
}

#[test]
fn com_optional_defaults_and_no_delegate_to_a_value_type_extension() {
    check(
        "ComOptionalDefaults",
        r#"
using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
static class Program
{
    static void A([Optional] object x) => Console.Write((x?.GetType().Name ?? "null") + " ");
    static void B([MarshalAs(UnmanagedType.Interface)][Optional] object x) => Console.Write((x?.GetType().Name ?? "null") + " ");
    static void C([IDispatchConstant][Optional] object x) => Console.Write((x?.GetType().Name ?? "null") + " ");
    static void D([IUnknownConstant][Optional] object x) => Console.Write((x?.GetType().Name ?? "null") + " ");
    static void Bar(Func<int, Action> x) => Console.WriteLine(1);
    static void Bar(Func<object, Action> x) => Console.WriteLine(2);
    static void Goo<T>(this T x) { }
    static void Main()
    {
        A(); B(); C(); D();
        Bar(x => x.Goo);
    }
}
"#,
        "Missing null DispatchWrapper UnknownWrapper 2\n",
    );
}

#[test]
fn marshal_as_is_a_field_marshal_row_and_com_defaults_cross_assemblies() {
    // `[MarshalAs]` is no attribute in metadata but a `FieldMarshal` row,
    // which a caller in another assembly reads: an `[Optional] T` marshalled
    // as `IDispatch` is left out as `null`, not `Missing`. `[Optional]
    // dynamic` is an `object` to all of it.
    check_with_library(
        "MarshalAsRows",
        r#"
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
public class P2<T>
{
    public int Foo([Optional][MarshalAs(UnmanagedType.IDispatch)] T i) => i == null ? 0 : 1;
}
public static class L
{
    public static string A([Optional] object x) => x?.GetType().Name ?? "null";
    public static string B([IUnknownConstant][Optional] object x) => x?.GetType().Name ?? "null";
    public static string C([IDispatchConstant][Optional] object x) => x?.GetType().Name ?? "null";
    public static string D([MarshalAs(UnmanagedType.Interface)][Optional] dynamic x) => ((object)x)?.GetType().Name ?? "null";
    public static string G([Optional] dynamic x) => ((object)x)?.GetType().Name ?? "null";
    public static void E([MarshalAs(UnmanagedType.LPArray, SizeParamIndex = 1, SizeConst = 3)] byte[] a, int n) { }
    [return: MarshalAs(UnmanagedType.LPWStr)]
    public static string F([MarshalAs(UnmanagedType.CustomMarshaler, MarshalType = "M", MarshalCookie = "c")] object o) => null;
}
"#,
        r#"
using System;
using System.Runtime.InteropServices;
class Program
{
    static void Main()
    {
        Console.WriteLine(new P2<object>().Foo());
        Console.WriteLine(L.A() + " " + L.B() + " " + L.C() + " " + L.D() + " " + L.G());
        var p = typeof(L).GetMethod("E").GetParameters()[0];
        var m = (MarshalAsAttribute)Attribute.GetCustomAttribute(p, typeof(MarshalAsAttribute));
        Console.WriteLine($"{p.Attributes} {m.Value} {m.ArraySubType} {m.SizeParamIndex} {m.SizeConst}");
        var f = typeof(L).GetMethod("F");
        var r = (MarshalAsAttribute)Attribute.GetCustomAttribute(f.ReturnParameter, typeof(MarshalAsAttribute));
        var c = (MarshalAsAttribute)Attribute.GetCustomAttribute(f.GetParameters()[0], typeof(MarshalAsAttribute));
        Console.WriteLine($"{f.ReturnParameter.Attributes} {r.Value} {c.Value} {c.MarshalType} {c.MarshalCookie}");
    }
}
"#,
        "0\nMissing UnknownWrapper DispatchWrapper null Missing\nHasFieldMarshal LPArray 80 1 3\n\
         HasFieldMarshal LPWStr CustomMarshaler M c\n",
    );
}

#[test]
fn pseudo_attributes_are_flags_columns_and_rows_by_what_they_are_on() {
    // What reflection reads off the rows csc writes: `[In]`, `[Out]`,
    // `[SpecialName]`, `[Serializable]`, `[NonSerialized]`, `[MethodImpl]`
    // and `[PreserveSig]` as flags, `[DefaultParameterValue]` as nothing but
    // the default, `[AssemblyVersion]` as the version, `HideBySig` on every
    // method, `BeginInvoke` and `EndInvoke` with `Invoke`'s parameters'
    // attributes but none of its defaults, and the assembly attributes
    // Roslyn adds of its own.
    check(
        "PseudoAttributes",
        r#"
using System;
using System.Linq;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
[assembly: AssemblyVersion("1.2.3.4")]
[Serializable]
public class C
{
    [NonSerialized] public int F;
    [SpecialName] public static void S() { }
    [MethodImpl(MethodImplOptions.NoInlining)] public static void N() { }
    [MethodImpl(MethodImplOptions.Synchronized)] public void Sy() { }
    [PreserveSig] public static void P() { }
    public static void M([In] int a, [Out] int[] b, [In, Out] ref int c, [Optional, DefaultParameterValue(7)] int d) { }
}
public delegate void D([In] ref int a, [Optional] int b, int c = 5, params int[] d);
class Program
{
    static string Attributes(ParameterInfo p) =>
        string.Join(",", p.GetCustomAttributes(false).Select(a => a.GetType().Name));
    static void Main()
    {
        var assembly = typeof(C).Assembly;
        Console.WriteLine(assembly.GetName().Version);
        Console.WriteLine(string.Join(",", assembly.GetCustomAttributesData().Select(a => a.AttributeType.Name)));
        Console.WriteLine(typeof(C).IsSerializable + " " + typeof(C).GetField("F").Attributes);
        foreach (var name in new[] { "S", "N", "Sy", "P", "M" })
        {
            var m = typeof(C).GetMethod(name);
            Console.WriteLine($"{name} {m.Attributes} {m.MethodImplementationFlags}");
        }
        foreach (var p in typeof(C).GetMethod("M").GetParameters())
            Console.WriteLine($"{p.Name} {p.Attributes} [{Attributes(p)}]");
        foreach (var name in new[] { "BeginInvoke", "EndInvoke" })
            foreach (var p in typeof(D).GetMethod(name).GetParameters())
                Console.WriteLine($"{name}.{p.Name} {p.Attributes} [{Attributes(p)}]");
    }
}
"#,
        "1.2.3.4\n\
         CompilationRelaxationsAttribute,RuntimeCompatibilityAttribute,DebuggableAttribute\n\
         True Public, NotSerialized\n\
         S Public, Static, HideBySig, SpecialName IL\n\
         N Public, Static, HideBySig NoInlining\n\
         Sy Public, HideBySig Synchronized\n\
         P Public, Static, HideBySig PreserveSig\n\
         M Public, Static, HideBySig IL\n\
         a In [InAttribute]\n\
         b Out [OutAttribute]\n\
         c In, Out [InAttribute,OutAttribute]\n\
         d Optional, HasDefault [OptionalAttribute]\n\
         BeginInvoke.a In [InAttribute]\n\
         BeginInvoke.b Optional [OptionalAttribute]\n\
         BeginInvoke.c None []\n\
         BeginInvoke.d None []\n\
         BeginInvoke.callback None []\n\
         BeginInvoke.object None []\n\
         EndInvoke.a In [InAttribute]\n\
         EndInvoke.result None []\n",
    );
}

#[test]
fn a_state_machine_is_named_by_its_members_place_and_disposed_of_only_inside_a_try() {
    // `<M>d__N` counts the members before `M`, and an explicit
    // implementation's name has its dots as `-`; a local function's machine
    // is `<...>d`. `Dispose` of an iterator stopped outside every `try`
    // leaves it as it was, as csc 8.0's does.
    check(
        "MachineNames",
        r#"
using System;
using System.Collections;
using System.Collections.Generic;
using System.Threading.Tasks;
class R : IDisposable { public void Dispose() => Console.Write("r "); }
public class C : IEnumerable<int>
{
    int f;
    public IEnumerable<int> P { get { yield return f; } }
    public async Task<int> A() { await Task.Yield(); return 1; }
    IEnumerator<int> IEnumerable<int>.GetEnumerator() { yield return 1; }
    IEnumerator IEnumerable.GetEnumerator() { yield return 2; }
    public static IEnumerable<int> D()
    {
        yield return 0;
        try { yield return 1; } finally { Console.Write("finally "); }
        using (new R()) { yield return 2; }
        yield return 3;
    }
}
class Program
{
    static void Main()
    {
        var c = new C();
        Console.WriteLine(c.P.GetType().Name);
        Console.WriteLine(((IEnumerable<int>)c).GetEnumerator().GetType().Name);
        Console.WriteLine(((IEnumerable)c).GetEnumerator().GetType().Name);
        IEnumerable<int> Local() { yield return 1; }
        Console.WriteLine(Local().GetType().Name);
        for (int k = 0; k <= 4; k++)
        {
            var e = C.D().GetEnumerator();
            for (int i = 0; i < k; i++) e.MoveNext();
            e.Dispose();
            var more = e.MoveNext();
            Console.WriteLine($"{k}: {more} {e.Current}");
        }
    }
}
"#,
        "<get_P>d__2\n\
         <System-Collections-Generic-IEnumerable<System-Int32>-GetEnumerator>d__4\n\
         <System-Collections-IEnumerable-GetEnumerator>d__5\n\
         <<Main>g__Local|0_0>d\n\
         0: True 0\n\
         1: True 1\n\
         finally 2: False 1\n\
         finally r 3: False 2\n\
         finally r 4: False 3\n",
    );
}

#[test]
fn nullable_annotations_are_written_as_csc_writes_them() {
    // `[Nullable]` gives each place of a declared type a byte — oblivious,
    // not annotated, annotated — and `[NullableContext]` on a type or a
    // method says the one most of its members agree on, so that they need
    // none of their own. What reflection and `NullabilityInfoContext` read
    // is what csc writes.
    check(
        "NullableMetadata",
        r#"
#nullable enable
using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;

public class C : List<string?>, IComparable<C?>
{
    public string? P { get; set; }
    public string Q { get; set; } = "";
    public (string, int?, object?) T;
    public string[]?[] Arr = new string[0][];
    public Dictionary<string, List<int?>>? D;
    public void F(object? x, object y, object z) { }
    public void G(Action<object?, Action<object, object?>?> c) { }
    public V R<V>(V v) => v;
    public T M<T>(T t) where T : class => t;
    public static C operator +(C a, C? b) => a;
    public int CompareTo(C? other) => 0;
    public IEnumerable<string?> Iter() { yield return null; }
}
public class Outer<T> where T : class { public class Inner { } public Inner? Make() => null; }
public delegate string? Del(object? o, string s);
#nullable disable
public class Old { public string X; }
#nullable enable
class Program
{
    static string Describe(IEnumerable<CustomAttributeData> attributes) =>
        string.Join(" ", attributes
            .Where(a => a.AttributeType.Name.StartsWith("Nullable"))
            .Select(a => a.AttributeType.Name.Replace("Attribute", "") + "(" + (a.ConstructorArguments[0].Value is System.Collections.ObjectModel.ReadOnlyCollection<CustomAttributeTypedArgument> list
                ? string.Join(",", list.Select(x => x.Value))
                : a.ConstructorArguments[0].Value) + ")"));
    static void Main()
    {
        var flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static | BindingFlags.DeclaredOnly;
        foreach (var type in new[] { typeof(C), typeof(Outer<>), typeof(Del), typeof(Old) })
        {
            Console.WriteLine($"{type.Name}: {Describe(type.GetCustomAttributesData())}");
            foreach (var field in type.GetFields(flags).OrderBy(f => f.Name))
                Console.WriteLine($"  field {field.Name}: {Describe(field.GetCustomAttributesData())}");
            foreach (var property in type.GetProperties(flags).OrderBy(p => p.Name))
                Console.WriteLine($"  property {property.Name}: {Describe(property.GetCustomAttributesData())}");
            foreach (var method in type.GetMethods(flags).OrderBy(m => m.Name))
            {
                Console.WriteLine($"  method {method.Name}: {Describe(method.GetCustomAttributesData())} returns {Describe(method.ReturnParameter.GetCustomAttributesData())}");
                foreach (var parameter in method.GetParameters())
                    Console.WriteLine($"    {parameter.Name}: {Describe(parameter.GetCustomAttributesData())}");
                foreach (var generic in method.IsGenericMethodDefinition ? method.GetGenericArguments() : Type.EmptyTypes)
                    Console.WriteLine($"    <{generic.Name}>: {Describe(generic.GetCustomAttributesData())}");
            }
        }
        var info = new NullabilityInfoContext().Create(typeof(C).GetMethod("F")!.GetParameters()[0]);
        Console.WriteLine(info.WriteState);
    }
}
"#,
        r#"C: NullableContext(1) Nullable(0,2)
  field <P>k__BackingField: Nullable(2)
  field <Q>k__BackingField: 
  field Arr: Nullable(1,2,1)
  field D: Nullable(2,1,1)
  field T: Nullable(0,1,2)
  property P: Nullable(2)
  property Q: 
  method CompareTo: NullableContext(2) returns 
    other: 
  method F:  returns 
    x: Nullable(2)
    y: 
    z: 
  method G:  returns 
    c: Nullable(1,2,2,1,2)
  method get_P: NullableContext(2) returns 
  method get_Q:  returns 
  method Iter:  returns Nullable(1,2)
  method M:  returns 
    t: 
    <T>: 
  method op_Addition:  returns 
    a: 
    b: Nullable(2)
  method R:  returns 
    v: 
    <V>: Nullable(2)
  method set_P: NullableContext(2) returns 
    value: 
  method set_Q:  returns 
    value: 
Outer`1: 
  method Make:  returns Nullable(2,0)
Del: 
  method BeginInvoke:  returns 
    o: Nullable(2)
    s: Nullable(1)
    callback: 
    object: 
  method EndInvoke:  returns Nullable(2)
    result: 
  method Invoke: NullableContext(2) returns 
    o: 
    s: Nullable(1)
Old: 
  field X: 
Nullable
"#,
    );
}

#[test]
fn what_the_language_writes_says_so_as_csc_writes_it() {
    // A static class is abstract and sealed; an iterator or an `async`
    // method keeps its own attributes and `[Extension]` and names its
    // machine; `in` and a `ref readonly` return are marked read-only; the
    // fields and accessors of an automatic property and of a field-like
    // event are compiler-generated, and an `init` one's field is readonly;
    // a record's own members come in Roslyn's order.
    // In a release build, as csc was asked for: a debug one hides the
    // fields from the debugger too.
    let options = rustlyn_semantics::CompilationOptions {
        optimize: true,
        ..Default::default()
    };
    check_with_options(
        "SynthesizedAttributes",
        rustlyn_syntax::LanguageVersion::CSharp11,
        options,
        r#"
using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Threading.Tasks;
[AttributeUsage(AttributeTargets.All)] public class AnyAttribute : Attribute { }
public static class Ext
{
    [Any] public static IEnumerable<T> Gen<T>(this IEnumerable<T> s) { foreach (var x in s) yield return x; }
    [Any] public static async Task<int> A() { await Task.Yield(); return 1; }
    public static ref readonly int RR(in int x, params int[] rest) => ref x;
}
public class C { public int Auto { get; set; } public int Init { get; init; } public event Action? E; }
public record R(int X);
class Program
{
    static string Names(IEnumerable<CustomAttributeData> attributes) => string.Join(",", attributes.Select(a => a.AttributeType.Name.Replace("Attribute", "")));
    static void Main()
    {
        var flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static | BindingFlags.DeclaredOnly;
        Console.WriteLine($"Ext: {typeof(Ext).IsAbstract} {typeof(Ext).IsSealed} [{Names(typeof(Ext).GetCustomAttributesData())}]");
        foreach (var name in new[] { "Gen", "A", "RR" })
        {
            var m = typeof(Ext).GetMethod(name)!;
            Console.WriteLine($"{name}: [{Names(m.GetCustomAttributesData())}] returns [{Names(m.ReturnParameter.GetCustomAttributesData())}] " +
                string.Join(" ", m.GetParameters().Select(p => $"{p.Name}[{Names(p.GetCustomAttributesData())}]")));
        }
        Console.WriteLine(Ext.Gen(new[] { 1 }).GetType().Name);
        foreach (var f in typeof(C).GetFields(flags).OrderBy(f => f.Name))
            Console.WriteLine($"{f.Name}: {f.IsInitOnly} [{Names(f.GetCustomAttributesData())}]");
        foreach (var m in typeof(C).GetMethods(flags).OrderBy(m => m.Name))
            Console.WriteLine($"{m.Name}: [{Names(m.GetCustomAttributesData())}]");
        Console.WriteLine(string.Join(" ", typeof(R).GetMethods(flags).Select(m => m.Name)));
    }
}
"#,
        r#"Ext: True True [Extension]
Gen: [IteratorStateMachine,Extension,Any] returns [] s[]
A: [AsyncStateMachine,Any] returns [] 
RR: [] returns [IsReadOnly] x[In,IsReadOnly] rest[ParamArray]
<Gen>d__0`1
<Auto>k__BackingField: False [CompilerGenerated]
<Init>k__BackingField: True [CompilerGenerated]
E: False [CompilerGenerated]
add_E: [CompilerGenerated]
get_Auto: [CompilerGenerated]
get_Init: [CompilerGenerated]
remove_E: [CompilerGenerated]
set_Auto: [CompilerGenerated]
set_Init: [CompilerGenerated]
get_EqualityContract get_X set_X ToString PrintMembers op_Inequality op_Equality GetHashCode Equals Equals <Clone>$ Deconstruct
"#,
    );
}

#[test]
fn required_members_ref_structs_and_records_say_so_to_other_compilers() {
    // `required` members are `[RequiredMember]`, and every constructor that
    // does not set them is an error to an older compiler; so is a `ref
    // struct`. A record's own members are annotated whatever the context,
    // and so is a `?` written outside `#nullable enable`.
    let options = rustlyn_semantics::CompilationOptions {
        optimize: true,
        ..Default::default()
    };
    check_with_options(
        "RequiredAndRefStructMarkers",
        rustlyn_syntax::LanguageVersion::CSharp11,
        options,
        r#"
using System;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Reflection;
public class Req { public required int A { get; init; } public required string B; public Req() { } [SetsRequiredMembers] public Req(int a) { A = a; B = ""; } }
public class Derived : Req { }
public ref struct RS { public int F; }
public record R(int X);
public class Q { public string? S; }
class Program
{
    static string Names(Type type, MemberInfo member) => string.Join(",", member.GetCustomAttributesData().Select(a =>
        a.AttributeType.Name.Replace("Attribute", "") + (a.ConstructorArguments.Count == 0 ? "" : "(" + string.Join(",", a.ConstructorArguments.Select(x => x.Value is string s ? s.Split(' ')[0] : x.Value)) + ")")));
    static void Main()
    {
        foreach (var type in new[] { typeof(Req), typeof(Derived), typeof(RS), typeof(R), typeof(Q) })
        {
            Console.WriteLine($"{type.Name}: {Names(type, type)}");
            var flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static | BindingFlags.DeclaredOnly;
            foreach (var member in type.GetMembers(flags).OrderBy(m => m.MetadataToken))
            {
                var names = Names(type, member);
                if (names.Length > 0) Console.WriteLine($"  {member.MemberType} {member.Name}({(member is MethodBase m ? m.GetParameters().Length : -1)}): {names}");
            }
        }
    }
}
"#,
        r#"Req: RequiredMember
  Field <A>k__BackingField(-1): CompilerGenerated
  Field B(-1): RequiredMember
  Method get_A(0): CompilerGenerated
  Method set_A(1): CompilerGenerated
  Constructor .ctor(0): Obsolete(Constructors,True),CompilerFeatureRequired(RequiredMembers)
  Constructor .ctor(1): SetsRequiredMembers
  Property A(-1): RequiredMember
Derived: 
  Constructor .ctor(0): Obsolete(Constructors,True),CompilerFeatureRequired(RequiredMembers)
RS: IsByRefLike,Obsolete(Types,True),CompilerFeatureRequired(RefStructs)
R: NullableContext(1),Nullable(0)
  Field <X>k__BackingField(-1): CompilerGenerated
  Method get_EqualityContract(0): CompilerGenerated
  Method get_X(0): CompilerGenerated
  Method set_X(1): CompilerGenerated
  Method ToString(0): CompilerGenerated
  Method PrintMembers(1): CompilerGenerated
  Method op_Inequality(2): NullableContext(2),CompilerGenerated
  Method op_Equality(2): NullableContext(2),CompilerGenerated
  Method GetHashCode(0): CompilerGenerated
  Method Equals(1): NullableContext(2),CompilerGenerated
  Method Equals(1): NullableContext(2),CompilerGenerated
  Method <Clone>$(0): CompilerGenerated
  Constructor .ctor(1): CompilerGenerated
  Method Deconstruct(1): CompilerGenerated
  Property EqualityContract(-1): CompilerGenerated
Q: 
  Field S(-1): Nullable(2)
"#,
    );
}

#[test]
fn a_record_copy_constructor_runs_no_initializers_and_with_reaches_a_long_tuples_rest() {
    check(
        "RecordCopyInit",
        r#"
public record C(int I)
{
    public int I { get; set; } = 42;
    public C(C c) { }
    public static void Main()
    {
        var c = new C(1);
        c.I = 2;
        var c2 = new C(c);
        var b = (1, 2, 3, 4, 5, 6, 7, 8, 9);
        var b2 = b with { Item7 = 42, Item8 = 43, Item9 = 44 };
        System.Console.WriteLine($"{(c.I, c2.I)} {b2.Item7}{b2.Item8}{b2.Item9}");
    }
}
"#,
        "(2, 0) 424344\n",
    );
}

#[test]
fn a_pattern_on_a_constant_that_cannot_fail_assigns_what_it_declares() {
    check(
        "ConstantPatternAssigns",
        r#"
class Program
{
    public static void Main()
    {
        const string s = "300";
        System.Console.Write(s is string { Length: int j });
        System.Console.WriteLine(" " + j);
    }
}
"#,
        "True 3\n",
    );
}

#[test]
fn null_compares_with_null_and_an_increment_steps_through_lifted_conversions() {
    check(
        "NullNullAndLiftedStep",
        r#"
struct T { }
class C
{
    public readonly int? i;
    public C(int? i) { this.i = i; }
    public static implicit operator int?(C c) => c.i;
    public static implicit operator C(long? s) => new C((int?)s);
    static void Main()
    {
        C c1 = new C(null);
        c1++;
        C c2 = new C(123);
        c2++;
        System.Console.WriteLine($"{c1.i == null} {c2.i} {default(T?) == null} {null != new T?()}");
    }
}
"#,
        "True 124 True False\n",
    );
}

#[test]
fn a_private_member_is_overridden_by_no_one_and_nameof_is_an_operator_beside_a_field() {
    check(
        "PrivateNotOverridden",
        r#"
using System;
class A
{
    public virtual string P { get { Console.Write("A.get "); return null; } set { Console.Write("A.set "); } }
}
class B : A
{
    public override string P { set { Console.Write("B.set "); } }
}
class C : B
{
    private new string P { get { Console.Write("C.get "); return null; } set { Console.Write("C.set "); } }
}
class D : C
{
    char nameof;
    public override string P { get { Console.Write("D.get "); return null; } }
    public void Test()
    {
        this.P = base.P;
        base.P = this.P;
        Console.WriteLine(nameof(nameof));
    }
}
class Program
{
    static void Main() => new D().Test();
}
"#,
        "A.get B.set D.get B.set nameof\n",
    );
}

#[test]
fn a_method_group_takes_a_type_parameter_its_class_constraint_makes_a_reference() {
    check(
        "GroupOfConstrainedT",
        r#"
using System;
class C { }
class D<T> where T : C
{
    public static void Test()
    {
        var t = (Action<T>)E.Target;
        t(null);
    }
}
static class E
{
    public static void Target(this C c) => Console.WriteLine("PASS");
}
class Program
{
    static void Main() => D<C>.Test();
}
"#,
        "PASS\n",
    );
}

#[test]
fn a_case_label_naming_a_nested_type_keeps_its_enclosing_construction() {
    check(
        "CaseNestedInConstructed",
        r#"
using System;
class G<T> { public class D { } }
class A { }
class B { }
class Program
{
    static string Test(object o)
    {
        switch (o)
        {
            case G<A>.D: return "A";
            case G<B>.D: return "B";
            default: return "none";
        }
    }
    static void Main()
    {
        Console.WriteLine(Test(new G<B>.D()));
        Console.WriteLine(Test(new G<A>.D()));
        Console.WriteLine(Test(1));
    }
}
"#,
        "B\nA\nnone\n",
    );
}

#[test]
fn an_extern_alias_is_a_namespace_a_using_directive_imports() {
    check_with_aliased_libraries(
        "UsingExternAlias",
        &[(
            r#"
public static class Extensions
{
    public static void Greet(this string text) => System.Console.WriteLine("hello " + text);
}
"#,
            &["lib"],
        )],
        r#"
extern alias lib;
using lib;

class Program
{
    static void Main() => "world".Greet();
}
"#,
        "hello world\n",
    );
}

#[test]
fn a_long_tuple_converts_element_by_element_into_its_nested_rest() {
    check(
        "LongTupleElementsConversion",
        r#"
using System;
class Program
{
    static void Show((long, long, long, long, long, long, long, long, object, long?) wide)
        => Console.WriteLine(wide);
    static void Main()
    {
        var narrow = (1, 2, 3, 4, 5, 6, 7, 8, "nine", 10);
        Show(narrow);
        (object, object, object, object, object, object, object, object, object, object, object, object, object, object, object) boxed =
            (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, (15, 16));
        Console.WriteLine(boxed.Item15);
    }
}
"#,
        "(1, 2, 3, 4, 5, 6, 7, 8, nine, 10)\n(15, 16)\n",
    );
}

#[test]
fn a_tuple_literal_reaches_an_implicit_operator_taking_a_tuple_its_constants_fit() {
    check(
        "TupleLiteralThroughOperator",
        r#"
using System;
class Program
{
    class Box
    {
        private (byte, string) value;
        private Box((byte, string) value) { this.value = value; }
        public static implicit operator Box((byte, string) value) => new Box(value);
        public override string ToString() => value.ToString();
    }
    static void Show(Box box) => Console.WriteLine(box);
    static Box Make() => (7, "made");
    static void Main()
    {
        Box declared = (1, "declared");
        Console.WriteLine(declared);
        declared = (300 - 45, null);
        Console.WriteLine(declared);
        Show((2, "argument"));
        Console.WriteLine(Make());
    }
}
"#,
        "(1, declared)\n(255, )\n(2, argument)\n(7, made)\n",
    );
}

#[test]
fn a_tuple_literal_without_a_type_asks_only_the_target_for_an_operator() {
    check(
        "TypelessTupleOperator",
        r#"
public class C
{
    static void Main()
    {
        C1 typeless = (1, null);
        System.Console.WriteLine(typeless.ToString());
        C1 typed = (1, "two");
        System.Console.WriteLine(typed.ToString());
    }

    public class C1
    {
        private (byte, string) val;
        public C1((byte, string) arg) { val = arg; }
        public static implicit operator C1((byte, string) arg)
        {
            System.Console.WriteLine("C1");
            return new C1(arg);
        }
        public override string ToString() => val.ToString();
    }
}

namespace System
{
    public struct ValueTuple<T1, T2>
    {
        public T1 Item1;
        public T2 Item2;
        public ValueTuple(T1 item1, T2 item2) { Item1 = item1; Item2 = item2; }
        public override string ToString() => "{" + Item1?.ToString() + ", " + Item2?.ToString() + "}";
        public static implicit operator C.C1((T1, T2) arg)
        {
            System.Console.WriteLine("VT");
            return new C.C1(((byte)(int)(object)arg.Item1, (string)(object)arg.Item2));
        }
    }
}
"#,
        "C1\n{1, }\nVT\n{1, two}\n",
    );
}

#[test]
fn a_nullable_boxes_to_a_type_parameter_its_underlying_type_depends_on() {
    check(
        "NullableToTypeParameter",
        r#"
class Holder<T, U> where T : struct, U where U : class
{
    public void Test(T t)
    {
        T? some = t;
        U boxed = some;
        System.Console.WriteLine(boxed.ToString());
        T? none = null;
        U empty = none;
        System.Console.WriteLine(empty == null);
    }
}
interface I { }
struct S : I { public override string ToString() => "boxed"; }
static class Program
{
    static void Main() => new Holder<S, I>().Test(default);
}
"#,
        "boxed\nTrue\n",
    );
}

#[test]
fn a_lifted_operand_takes_the_conversion_giving_the_nullable_itself() {
    check(
        "LiftedOperandConversion",
        r#"
using System;
struct S
{
    public static implicit operator int(S n) { Console.Write("int "); return 0; }
    public static implicit operator int?(S n) { Console.Write("int? "); return null; }
}
struct Conv
{
    public static implicit operator int(Conv c) => 1;
    public static implicit operator double?(Conv c) => 123.0;
}
class Program
{
    static void Main()
    {
        int? nullable = 5;
        int plain = 1;
        S s = default;
        var lifted = nullable + s;
        var unlifted = plain + s;
        Console.WriteLine(lifted.HasValue + " " + unlifted);
        Conv? c = new Conv();
        double? d = c;
        Console.WriteLine(d);
        c = null;
        d = c;
        Console.WriteLine(d.HasValue);
    }
}
"#,
        "int? int False 1\n123\nFalse\n",
    );
}

#[test]
fn a_narrowing_cast_of_a_constant_is_a_constant_of_the_narrower_type() {
    check(
        "NarrowedConstant",
        r#"
using System;
class Program
{
    static bool Is42(byte b) => b is 42;
    static void Main()
    {
        byte x = (int)42L;
        Console.WriteLine(x);
        Console.WriteLine(Is42((int)42L));
        Console.WriteLine(Is42((int)43L));
        short s = unchecked((int)0x1_0000_0005L);
        Console.WriteLine(s);
    }
}
"#,
        "42\nTrue\nFalse\n5\n",
    );
}

#[test]
fn a_switch_argument_reaches_a_parameter_every_arm_reaches() {
    check(
        "SwitchArmsOverload",
        r#"
using System;
class Program
{
    static void Main()
    {
        bool b = true;
        One(b switch { false => 1, true => 2 });
        Two(b switch { false => 1, true => 2 });
        Two(b switch { false => 1, true => 100_000 });
    }
    static void One(short s) => Console.WriteLine("one short " + s);
    static void Two(short s) => Console.WriteLine("short " + s);
    static void Two(long l) => Console.WriteLine("long " + l);
}
"#,
        "one short 2\nshort 2\nlong 100000\n",
    );
}

#[test]
fn an_or_pattern_leaves_the_alternative_every_other_reaches_by_reference_or_boxing() {
    check(
        "OrPatternNarrowing",
        r#"
using System;
class Program
{
    static void Main()
    {
        object o = new Derived1();
        { if (o is (Derived1 or Derived2 or Base) and var i) M(i); }
        { if (o is ((Derived1 or Derived2) or Base) and var i) M(i); }
        { if (o is (Derived1 or Derived2) and var i) M(i); }
        o = 1;
        { if (o is (int or long) and var i) M(i); }
        { if (o is (long or IComparable) and var i) M(i); }
        Console.WriteLine(nameof(G<Base, Derived1>));
    }
    static void M<T>(T t) => Console.WriteLine(typeof(T));
}
class Base { }
class Derived1 : Base { }
class Derived2 : Base { }
class G<A, B> { }
"#,
        "Base\nBase\nSystem.Object\nSystem.Object\nSystem.IComparable\nG\n",
    );
}

#[test]
fn a_coalesce_that_throws_an_awaited_exception_throws_it_where_the_left_is_null() {
    check(
        "CoalesceThrowAwait",
        r#"
using System;
using System.Threading.Tasks;
class Program
{
    static void Main() => Run().Wait();
    static async Task Run()
    {
        foreach (var i in new[] { 1, 2 })
        {
            try
            {
                var used = (await Get(i))?.ToString() ?? throw await Make(i);
                Console.WriteLine("got " + used);
            }
            catch (Exception ex)
            {
                Console.WriteLine("thrown " + ex.Message);
            }
        }
    }
    static async Task<object> Get(int i)
    {
        await Task.Yield();
        return i == 1 ? i : null;
    }
    static async Task<Exception> Make(int i)
    {
        await Task.Yield();
        return new Exception(i.ToString());
    }
}
"#,
        "got 1\nthrown 2\n",
    );
}

#[test]
fn a_lambda_returning_a_switch_fits_only_a_delegate_every_arm_reaches() {
    check(
        "SwitchLambdaOverload",
        r#"
using System;
class Program
{
    static void Main()
    {
        var s1 = new Source1();
        var s2 = new Source2();
        foreach (var b in new[] { false, true })
            M(() => b switch { false => s1, true => s2 });
        Console.WriteLine();
    }
    static void M(Func<Source1> s) => throw null;
    static void M(Func<Source2> s) => throw null;
    static void M(Func<Target> t) => Console.Write(t());
}
class Target
{
    private readonly string value;
    public Target(string value) => this.value = value;
    public override string ToString() => value;
}
class Source1 { public static implicit operator Target(Source1 s) => new Target("one "); }
class Source2 { public static implicit operator Target(Source2 s) => new Target("two "); }
"#,
        "one two \n",
    );
}

#[test]
fn a_method_group_converts_up_to_tuple_names_and_dynamic() {
    check(
        "GroupIdentityConversion",
        r#"
using System;
class Program
{
    static void F<T>(T t) { }
    static void Main()
    {
        Action<(int X, object Y)> a = F<(int, dynamic)>;
        var both = new[] { F<(int X, object Y)>, F<(int, dynamic)> };
        Console.WriteLine(a.GetType());
        Console.WriteLine(both[1].GetType());
    }
}
"#,
        "System.Action`1[System.ValueTuple`2[System.Int32,System.Object]]\nSystem.Action`1[System.ValueTuple`2[System.Int32,System.Object]]\n",
    );
}

#[test]
fn a_type_parameter_an_expression_type_constrains_infers_a_tree_from_a_lambda() {
    check(
        "ExpressionConstrainedInference",
        r#"
using System;
using System.Linq.Expressions;
class A<T>
{
    public static U F<U>(U u) where U : T => u;
}
class Program
{
    static T Tree<T>(T t) where T : Expression => t;
    static T Plain<T>(T t) where T : Delegate => t;
    static void Main()
    {
        Report(Tree(() => 1));
        Report(Plain((int i) => { }));
        Report(A<LambdaExpression>.F(() => 1));
        Report(A<object>.F(() => 1));
    }
    static void Report(object value) => Console.WriteLine(value is Expression ? "tree " + value : value.GetType().ToString());
}
"#,
        "tree () => 1\nSystem.Action`1[System.Int32]\ntree () => 1\nSystem.Func`1[System.Int32]\n",
    );
}

#[test]
fn a_value_compared_with_null_is_the_constant_the_lifted_comparison_gives() {
    check(
        "ValueEqualsNull",
        r#"
using System;
class Program
{
    static int F() { Console.Write("F "); return 0; }
    static void Main()
    {
        int i = 0;
        Guid g = default;
        Console.WriteLine(i == null);
        Console.WriteLine(i != null);
        Console.WriteLine(null == g);
        Console.WriteLine(F() == null);
    }
}
"#,
        "False\nTrue\nFalse\nF False\n",
    );
}

#[test]
fn a_get_enumerator_giving_nothing_leaves_the_loop_to_the_interface() {
    check(
        "VoidGetEnumerator",
        r#"
using System;
using System.Collections;
class Base
{
    public Enumerator GetEnumerator() { Console.WriteLine("base"); return new Enumerator(); }
}
class Enumerator
{
    public bool MoveNext() => false;
    public int Current => 0;
}
class Derived : Base, IEnumerable
{
    IEnumerator IEnumerable.GetEnumerator() { Console.WriteLine("interface"); return new object[] { 1 }.GetEnumerator(); }
    new public void GetEnumerator() { Console.WriteLine("wrong"); }
}
class Program
{
    static void Main()
    {
        foreach (int i in new Derived()) Console.WriteLine(i);
    }
}
"#,
        "interface\n1\n",
    );
}

#[test]
fn a_conditional_access_whose_call_is_conditioned_out_goes_as_a_whole() {
    check(
        "ConditionedOutAccess",
        r#"
class Program
{
    static void Main()
    {
        Probe.Create()?.Test();
        Probe.Create()?.Self().Test();
        Probe.Create()?.Self()?.Test();
        System.Console.WriteLine("done");
    }
}
class Probe
{
    [System.Diagnostics.Conditional("NOWHERE")]
    public void Test() => System.Console.WriteLine("Test");
    public static Probe Create() { System.Console.WriteLine("Create"); return new Probe(); }
    public Probe Self() { System.Console.WriteLine("Self"); return this; }
}
"#,
        "done\n",
    );
}

#[test]
fn several_conditional_attributes_read_from_a_library_keep_a_call_any_of_them_allows() {
    check_with_library(
        "SeveralConditionsFromMetadata",
        r#"
#define ONE
#define TWO
using System.Diagnostics;
public static class Traced
{
    [Conditional("ONE"), Conditional("TWO")]
    public static void Either() => System.Console.WriteLine("either");
    [Conditional("THREE"), Conditional("FOUR")]
    public static void Neither() => System.Console.WriteLine("neither");
}
"#,
        r#"
#define TWO
class Program
{
    static void Main()
    {
        Traced.Either();
        Traced.Neither();
    }
}
"#,
        "either\n",
    );
}

#[test]
fn a_foreach_variable_takes_each_element_through_an_operator_its_type_declares() {
    check(
        "ForEachThroughOperator",
        r#"
using System;
using System.Collections.Generic;
struct Wrapped
{
    public int V;
    public static implicit operator Wrapped(int x) { Console.Write("implicit "); return new Wrapped { V = x }; }
}
class Named
{
    public string Name;
    public static explicit operator Named(string s) { Console.Write("explicit "); return new Named { Name = s }; }
}
class Program
{
    static void Main()
    {
        foreach (Wrapped w in new[] { 10, 20 }) Console.WriteLine(w.V);
        foreach (Named n in new List<string> { "a" }) Console.WriteLine(n.Name);
        foreach (long l in new[] { 1 }) Console.WriteLine(l);
    }
}
"#,
        "implicit 10\nimplicit 20\nexplicit a\n1\n",
    );
}

#[test]
fn a_call_through_a_read_only_place_works_on_a_copy() {
    check(
        "ReadOnlyPlaceCopies",
        r#"
using System;
struct Counter
{
    public int X;
    public void Bump() => X++;
    public override string ToString() => (X++).ToString();
}
class Holder<T>
{
    readonly T t;
    public Holder(T t) => this.t = t;
    public void Print()
    {
        Console.WriteLine(t?.ToString());
        Console.WriteLine(t?.ToString());
    }
}
class Program
{
    static void Main()
    {
        new Holder<Counter>(default).Print();
        Counter a = default, b = default;
        ref readonly Counter ro = ref b;
        bool pick = false;
        (pick ? ref a : ref ro).Bump();
        (!pick ? ref a : ref ro).Bump();
        (pick ? ref a : ref b).Bump();
        Console.WriteLine(a.X + " " + b.X);
    }
}
"#,
        "0\n0\n0 1\n",
    );
}

#[test]
fn a_call_on_a_refvalue_reaches_the_variable_it_refers_to() {
    check(
        "RefValueReceiver",
        r#"
struct Box<T>
{
    public T X;
    public void Assign(T value) => X = value;
}
class Program
{
    static void Main()
    {
        var box = new Box<int>();
        var reference = __makeref(box);
        __refvalue(reference, Box<int>).Assign(333);
        System.Console.WriteLine(box.X);
        var nested = new Box<Box<int>>();
        reference = __makeref(nested);
        __refvalue(reference, Box<Box<int>>).X.Assign(42);
        System.Console.WriteLine(nested.X.X);
    }
}
"#,
        "333\n42\n",
    );
}

#[test]
fn an_expression_tree_reaches_an_interface_member_of_a_type_parameter_through_a_convert() {
    check(
        "TreeInterfaceConvert",
        r#"
using System;
using System.Linq.Expressions;
interface IHas { int Value { get; } }
class Has : IHas { public int Value { get; set; } }
class Program
{
    static Expression<Func<T, int>> Interface<T>() where T : IHas => x => x.Value;
    static Expression<Func<T, int>> Class<T>() where T : class, IHas => x => x.Value;
    static void Main()
    {
        Console.WriteLine(Interface<Has>().Body);
        Console.WriteLine(Class<Has>().Body);
    }
}
"#,
        "Convert(x, IHas).Value\nx.Value\n",
    );
}

#[test]
fn a_lambda_or_local_function_made_a_method_of_the_type_is_marked_compiler_generated() {
    check(
        "ClosureMethodsGenerated",
        r#"
using System;
using System.Linq;
using System.Reflection;
class Program
{
    int f = 1;
    static void Main()
    {
        new Program().Run();
        foreach (var m in typeof(Program).GetMethods(BindingFlags.NonPublic | BindingFlags.Static | BindingFlags.Instance | BindingFlags.DeclaredOnly).OrderBy(m => m.Name))
            Console.WriteLine(m.Name + ": " + string.Join(",", m.GetCustomAttributes(false).Select(a => a.GetType().Name)));
    }
    void Run()
    {
        int Local(int x) => x + 1;
        Func<int> g = () => f;
        Console.WriteLine(Local(1) + g());
    }
}
"#,
        "3\n<Run>b__2_1: CompilerGeneratedAttribute\n<Run>g__Local|2_0: CompilerGeneratedAttribute\nMain: \nRun: \n",
    );
}

#[test]
fn an_index_no_int_reaches_goes_to_the_indexer_an_inline_array_declares() {
    check(
        "InlineArrayOwnIndexer",
        r#"
[System.Runtime.CompilerServices.InlineArray(4)]
struct Buffer4
{
    private int _element0;
    public string this[nint i] => "nint";
}
class Program
{
    static void Main()
    {
        Buffer4 b = default;
        b[1] = 5;
        System.Console.WriteLine(b[(nint)0]);
        System.Console.WriteLine(b[1]);
    }
}
"#,
        "nint\n5\n",
    );
}

#[test]
fn a_caller_attribute_whose_value_the_parameter_cannot_take_is_ignored() {
    check_with_il_library(
        "IgnoredCallerInfo",
        r#"
.class public auto ansi beforefieldinit Logger extends [mscorlib]System.Object
{
    .method public hidebysig static void Line([opt] string line) cil managed
    {
        .param [1] = "hello"
        .custom instance void [mscorlib]System.Runtime.CompilerServices.CallerLineNumberAttribute::.ctor() = ( 01 00 00 00 )
        ldstr "line: " ldarg.0 call string [mscorlib]System.String::Concat(string, string)
        call void [mscorlib]System.Console::WriteLine(string) ret
    }
    .method public hidebysig specialname rtspecialname instance void .ctor() cil managed
    { ldarg.0 call instance void [mscorlib]System.Object::.ctor() ret }
}
"#,
        r#"
class Program
{
    static void Main() => Logger.Line();
}
"#,
        "line: hello\n",
    );
}

#[test]
fn a_null_no_attribute_blob_can_name_the_type_of_is_written_as_null() {
    check(
        "UnnameableNullArgument",
        r#"
using System;
using System.Linq;
class A : Attribute { public A(object o) { } }
class B<T> { }
[A(default(B<int>))]
class C { }
class Program
{
    static void Main()
    {
        var attribute = typeof(C).CustomAttributes.Single(d => d.AttributeType == typeof(A));
        Console.WriteLine(attribute.ConstructorArguments.Single().Value is null);
    }
}
"#,
        "True\n",
    );
}

#[test]
fn a_date_time_constant_no_date_time_can_hold_is_no_default() {
    check_with_il_library(
        "BadDateTimeConstant",
        r#"
.class public auto ansi beforefieldinit Holder extends [mscorlib]System.Object
{
    .method public hidebysig static valuetype [mscorlib]System.DateTime Pass([opt] valuetype [mscorlib]System.DateTime p) cil managed
    {
        .param [1]
        .custom instance void [mscorlib]System.Runtime.CompilerServices.DateTimeConstantAttribute::.ctor(int64) = ( 01 00 FF FF FF FF FF FF FF FF 00 00 )
        ldarg.0 ret
    }
    .method public hidebysig specialname rtspecialname instance void .ctor() cil managed
    { ldarg.0 call instance void [mscorlib]System.Object::.ctor() ret }
}
"#,
        r#"
class Program
{
    static void Main() => System.Console.WriteLine(Holder.Pass().Ticks);
}
"#,
        "0\n",
    );
}

#[test]
fn a_candidate_inferring_a_pointer_type_argument_gives_way() {
    check(
        "PointerTypeArgument",
        r#"
public class Program
{
    static unsafe void Main()
    {
        int* p = null;
        M(p, 0);
    }
    static void M<T>(T t, int i) => System.Console.WriteLine("generic");
    static void M(C c, short s) => System.Console.WriteLine("converted");
}
public class C { public static unsafe implicit operator C(int* p) => null; }
"#,
        "converted\n",
    );
}

#[test]
fn a_call_on_an_element_of_a_rectangular_array_of_t_skips_the_type_check() {
    check(
        "RectangularCovariantElement",
        r#"
class Program
{
    static string Name<T>(T[,] array) => array[0, 0].GetType().Name;
    static void Main() => System.Console.WriteLine(Name<object>(new string[,] { { "" } }));
}
"#,
        "String\n",
    );
}

#[test]
fn a_float_wrapped_into_a_native_integer_nullable_is_converted_first() {
    check(
        "FloatToNullableNativeInt",
        r#"
using System;
class Program
{
    static void Main()
    {
        float f = 5.7f;
        double d = 6.2;
        IntPtr? n = (IntPtr?)f;
        UIntPtr? u = (UIntPtr?)d;
        Console.WriteLine(n + " " + u);
    }
}
"#,
        "5 6\n",
    );
}

#[test]
fn a_query_clause_calls_a_method_with_optional_parameters_from_its_own_line() {
    check(
        "QueryClauseCallerLine",
        r#"
using System;
using System.Runtime.CompilerServices;
class Source
{
    public Source Where(Func<object, bool> predicate, [CallerLineNumber] int line = -1)
    {
        Console.WriteLine("where " + line + " " + predicate(this));
        return this;
    }
    public string Select(Func<object, object> selector, [CallerLineNumber] int line = -1)
        => "select " + line + " " + selector(this);
}
class Program
{
    static void Main()
    {
        var q = from x in new Source()
                where x != null
                select x.GetType().Name;
        Console.WriteLine(q);
    }
}
"#,
        "where 19 True\nselect 20 Source\n",
    );
}

#[test]
fn a_query_invokes_a_where_held_in_a_delegate_property() {
    check(
        "QueryDelegateWhere",
        r#"
var x = from i in new C()
        where i is not null
        select i;
System.Console.WriteLine(x);

public class C
{
    public System.Func<System.Func<C, bool>, C> Where =>
        (System.Func<C, bool> f) => { System.Console.Write(f(this)); return this; };
}
"#,
        "TrueC\n",
    );
}

#[test]
fn a_nested_type_hides_only_one_of_its_own_arity() {
    check(
        "NestedTypeArity",
        r#"
using System;
class Base
{
    public class Type<T> { public static void Method() => Console.WriteLine("Base.Type<T>"); }
    public class Derived : Base
    {
        public class Type<T, U> { public static void Method() => Console.WriteLine("Derived.Type<T, U>"); }
    }
}
class Program
{
    static void Main()
    {
        Base.Derived.Type<int>.Method();
        Base.Derived.Type<int, long>.Method();
    }
}
"#,
        "Base.Type<T>\nDerived.Type<T, U>\n",
    );
}

#[test]
fn a_lambda_in_a_field_initializer_declares_local_functions_generic_ones_too() {
    check(
        "InitializerLocalFunctions",
        r#"
using System;
class C<T>
{
    internal static Func<Delegate> F = () =>
    {
        return Outer<int>();
        static Delegate Outer<U>()
        {
            return Inner<double>();
            static Delegate Inner<V>()
            {
                Func<T, U> d = (T t) => { Console.WriteLine((typeof(T), typeof(U))); return default; };
                d.Invoke(default);
                return d;
            }
        }
    };
    Func<int> G = () => { return Local(); int Local() => 7; };
    public int RunG() => G();
}
class Program
{
    static void Main()
    {
        Console.WriteLine(C<string>.F().GetType());
        Console.WriteLine(new C<string>().RunG());
    }
}
"#,
        "(System.String, System.Int32)\nSystem.Func`2[System.String,System.Int32]\n7\n",
    );
}

#[test]
fn a_dynamic_compound_add_subscribes_where_the_member_is_an_event() {
    check(
        "DynamicEventCompound",
        r#"
using System;
class Target
{
    public int Property
    {
        get { Console.WriteLine("get"); return 0; }
        set { Console.WriteLine("set " + value); }
    }
    public event EventHandler<object> Event
    {
        add { Console.WriteLine("add"); }
        remove { Console.WriteLine("remove"); }
    }
}
class Program
{
    static dynamic Make() { Console.WriteLine("make"); return new Target(); }
    static EventHandler<object> Handler() { Console.WriteLine("handler"); return (a, b) => { }; }
    static int One() { Console.WriteLine("one"); return 1; }
    static void Main()
    {
        Make().Property += One();
        Make().Event += Handler();
        Make().Event -= Handler();
    }
}
"#,
        "make\nget\none\nset 1\nmake\nhandler\nadd\nmake\nhandler\nremove\n",
    );
}

#[test]
fn a_group_with_explicit_type_arguments_leaves_out_methods_they_break() {
    check(
        "GroupExplicitConstraints",
        r#"
var x = new object().M<int>;
x();
System.Console.WriteLine(Concat().Length);
static System.ReadOnlySpan<byte> Concat() => "1"u8 + checked("2"u8 + unchecked("3"u8 + "4"u8));

public static class E1
{
    public static void M<T>(this object o) where T : class { }
}
public static class E2
{
    public static void M<T>(this object o) { System.Console.WriteLine("ran"); }
}
"#,
        "ran\n4\n",
    );
}

#[test]
fn an_expression_tree_writes_a_lifted_user_defined_operator_as_the_operator() {
    check(
        "TreeLiftedOperator",
        r#"
using System;
using System.Linq.Expressions;
struct B
{
    public static implicit operator int?(B x) => 1;
    public static int operator +(B x, int y) => 2 + y;
    public static bool operator <(B x, int y) => true;
    public static bool operator >(B x, int y) => false;
    static object F(object o) => o;
    static void Main()
    {
        Expression<Func<B, int?>> f = x => x + x;
        Console.WriteLine(f);
        Console.WriteLine(f.Compile()(new B()));
        Expression<Func<B?, int?, bool>> g = (x, y) => x < y;
        Console.WriteLine(g.Compile()(new B(), 1) + " " + g.Compile()(null, 1));
        Expression<Func<string, object>> h = s => checked(F(s));
        Console.WriteLine(h);
    }
}
"#,
        "x => (Convert(x, Nullable`1) + Convert(x, Nullable`1))\n3\nTrue False\ns => F(s)\n",
    );
}

#[test]
fn a_dynamic_argument_passed_by_reference_leaves_the_call_static() {
    check(
        "RefDynamicArgument",
        r#"
public class C
{
    public static void Main()
    {
        dynamic d = "qq";
        System.Console.WriteLine(F(ref d));
    }
    public static dynamic F(ref dynamic d)
    {
        ref var first = ref Pass(ref d.Length);
        d = "qwerty";
        ref var second = ref Pass(ref d.Length);
        return first;
    }
    public static ref dynamic Pass(ref dynamic d) => ref d;
}
"#,
        "2\n",
    );
}

#[test]
fn dynamic_flags_that_do_not_fit_the_type_are_ignored_and_a_ref_tuple_passes_through() {
    check_with_il_library(
        "ShortDynamicFlags",
        r#"
.class public auto ansi beforefieldinit Holder extends [mscorlib]System.Object
{
    .field static valuetype [mscorlib]System.ValueTuple`2<int32, object> 'value'
    .method public hidebysig newslot virtual instance valuetype [mscorlib]System.ValueTuple`2<int32, object>& Get(int32 arg) cil managed
    {
        .param [0]
        .custom instance void [mscorlib]System.Runtime.CompilerServices.DynamicAttribute::.ctor(bool[]) = ( 01 00 03 00 00 00 00 00 01 00 00 )
        ldsflda valuetype [mscorlib]System.ValueTuple`2<int32, object> Holder::'value'
        ldarg.1
        box [mscorlib]System.Int32
        stfld !1 valuetype [mscorlib]System.ValueTuple`2<int32, object>::Item2
        ldsflda valuetype [mscorlib]System.ValueTuple`2<int32, object> Holder::'value'
        ret
    }
    .method public hidebysig specialname rtspecialname instance void .ctor() cil managed
    { ldarg.0 call instance void [mscorlib]System.Object::.ctor() ret }
}
"#,
        r#"
class Derived : Holder
{
    public override ref (int, dynamic) Get(int arg) => ref base.Get(arg);
}
class Program
{
    static void Main()
    {
        ref var x = ref new Derived().Get(42);
        System.Console.Write(x.Item2);
        x.Item2 = "qq";
        System.Console.WriteLine(x.Item2);
    }
}
"#,
        "42qq\n",
    );
}

#[test]
fn a_dynamic_call_by_simple_name_reaches_an_enclosing_types_methods_on_the_type() {
    check(
        "DynamicOuterSimpleName",
        r#"
public class A
{
    public static void M(int x) => System.Console.WriteLine("int " + x);
    public static void M(string x) => System.Console.WriteLine("string " + x);
    public class B
    {
        public void F()
        {
            dynamic d = 5;
            M(d);
            d = "five";
            M(d);
        }
    }
    public static void Main() => new A.B().F();
}
"#,
        "int 5\nstring five\n",
    );
}

#[test]
fn a_static_left_of_a_dynamic_logical_operator_is_asked_by_its_own_true_or_false() {
    check(
        "StaticLeftDynamicLogic",
        r#"
public struct S
{
    public static S operator &(S x, S y) { System.Console.Write("and "); return x; }
    public static S operator |(S x, S y) { System.Console.Write("or "); return x; }
    public static bool operator false(S? x) { System.Console.Write("false? "); return true; }
    public static bool operator true(S? x) { System.Console.Write("true? "); return true; }
}
class Program
{
    static void Main()
    {
        var s = new S();
        dynamic a = s && (dynamic)s;
        System.Console.WriteLine(a is S);
        dynamic b = s || (dynamic)s;
        System.Console.WriteLine(b is S);
    }
}
"#,
        "false? True\ntrue? True\n",
    );
}

#[test]
fn a_lambda_returning_a_reference_has_the_delegate_type_a_method_like_it_has() {
    check(
        "RefLambdaNaturalType",
        r#"
using System;
class Program
{
    static ref int F(ref int x, ref int y) => ref x;
    static void Main()
    {
        var method = F;
        var lambda = (ref int x, ref int y) => ref x;
        Console.WriteLine(method.GetType() == lambda.GetType());
        int a = 1, b = 2;
        lambda(ref a, ref b) = 5;
        Console.WriteLine(a);
    }
}
"#,
        "True\n5\n",
    );
}

#[test]
fn a_param_array_attribute_on_no_array_makes_no_params() {
    check_with_il_library(
        "ParamsOnNoArray",
        r#"
.class public auto ansi beforefieldinit C extends [mscorlib]System.Object
{
    .method public hidebysig static void M(int32 x) cil managed
    {
        .param [1]
        .custom instance void [mscorlib]System.ParamArrayAttribute::.ctor() = ( 01 00 00 00 )
        ret
    }
    .method public hidebysig specialname rtspecialname instance void .ctor() cil managed
    { ldarg.0 call instance void [mscorlib]System.Object::.ctor() ret }
}
"#,
        r#"
var m = C.M;
System.Console.WriteLine(m.GetType());
"#,
        "System.Action`1[System.Int32]\n",
    );
}

#[test]
fn a_compound_assignment_widens_an_unsigned_operand_without_its_sign() {
    check(
        "CompoundUnsignedWidening",
        r#"
class Program
{
    static void Main()
    {
        uint u = 0xFFFFFFFF;
        ulong ul = ulong.MaxValue;
        long l = 0;
        double d = 0;
        float f = 0;
        l += u;
        d += u;
        f += u;
        d += ul;
        ushort us = 65535;
        l += us;
        long signed = -5;
        signed += (sbyte)-1;
        System.Console.WriteLine(l + " " + d + " " + f + " " + signed);
    }
}
"#,
        "4295032830 1.844674407800452E+19 4.2949673E+09 -6\n",
    );
}

#[test]
fn an_async_iterator_keeps_an_unmanaged_current_while_it_waits() {
    check(
        "UnmanagedCurrentKept",
        r#"
using System.Threading.Tasks;
using System.Collections.Generic;

var source = new TaskCompletionSource();
var walk = C.M<int>(source.Task, 42).GetAsyncEnumerator();
await walk.MoveNextAsync();
var next = walk.MoveNextAsync();
System.Console.WriteLine(walk.Current.field);
source.SetResult();
await next;
System.Console.WriteLine(walk.Current.field);

public struct S<T> where T : unmanaged { public T field; }
public class C
{
    public static async IAsyncEnumerable<S<T>> M<T>(Task t, T value) where T : unmanaged
    {
        yield return new S<T> { field = value };
        await t;
        yield return default;
    }
}
"#,
        "42\n0\n",
    );
}

#[test]
fn a_range_assigned_through_a_slice_returning_a_reference_is_a_variable() {
    check(
        "SliceRefAssignment",
        r#"
class C
{
    public int Length => 5;
    public ref int Slice(int start, int length) { System.Console.Write($"Slice({start},{length}) "); return ref Driver.Result; }
}
class Driver
{
    public static int Result;
    static void Main()
    {
        var c = new C();
        c[1..] = 42;
        System.Console.WriteLine(Result);
    }
}
"#,
        "Slice(1,4) 42\n",
    );
}

#[test]
fn a_generic_class_forwards_an_interface_member_to_a_base_or_to_its_own_modified_override() {
    check_with_il_library(
        "GenericForwarders",
        r#"
.class public auto ansi beforefieldinit Base`1<T> extends [mscorlib]System.Object
{
    .method public hidebysig newslot virtual instance !T modopt([mscorlib]System.Runtime.CompilerServices.IsConst) V(!T modopt([mscorlib]System.Runtime.CompilerServices.IsConst) t) cil managed
    { ldstr "Base.V" call void [mscorlib]System.Console::WriteLine(string) ldarg.1 ret }
    .method public hidebysig instance !T M(!T t) cil managed
    { ldstr "Base.M" call void [mscorlib]System.Console::WriteLine(string) ldarg.1 ret }
    .method public hidebysig specialname rtspecialname instance void .ctor() cil managed
    { ldarg.0 call instance void [mscorlib]System.Object::.ctor() ret }
}
"#,
        r#"
using System;
public interface I<T>
{
    T M(T t);
    T V(T t);
}
public class Sub<T> : Base<T>, I<T>
{
    public override T V(T t) { Console.WriteLine("Sub.V"); return base.V(t); }
}
class Program
{
    static void Main()
    {
        I<string> i = new Sub<string>();
        Console.WriteLine(i.M("m"));
        Console.WriteLine(i.V("v"));
    }
}
"#,
        "Base.M\nm\nSub.V\nBase.V\nv\n",
    );
}

#[test]
fn a_record_over_a_referenced_record_inherits_its_accessible_members_and_sealed_to_string() {
    check_with_library(
        "RecordOverReference",
        r#"
public record A
{
    public object P1 { get; }
    internal object P2 { get; }
    public sealed override string ToString() => "A";
}
public record B : A
{
    internal new object P1 { get; }
    public new object P2 { get; }
}
"#,
        r#"
record C(object P1, object P2, object P3) : B;
class Program
{
    static void Main()
    {
        var c = new C(1, 2, 3);
        System.Console.WriteLine("({0}, {1}, {2}) {3}", c.P1, c.P2, c.P3, c);
    }
}
"#,
        "(, , 3) A\n",
    );
}

#[test]
fn a_record_overrides_an_abstract_property_a_referenced_record_names_its_own_way() {
    check_with_il_library(
        "RecordOverRenamedAccessors",
        r#"
.class public System.Runtime.CompilerServices.IsExternalInit
{
  .method public hidebysig specialname rtspecialname instance void .ctor() { ldnull throw }
}
.class public abstract A
{
  .method family hidebysig specialname rtspecialname instance void .ctor()
  { ldarg.0 call instance void [mscorlib]System.Object::.ctor() ret }
  .method family hidebysig specialname rtspecialname instance void .ctor(class A A_1) { ldnull throw }
  .method public hidebysig newslot specialname abstract virtual instance class A '<Clone>$'() { }
  .property instance class [mscorlib]System.Type EqualityContract()
  {
    .get instance class [mscorlib]System.Type A::GetProperty1()
  }
  .property instance object modopt(uint16) P()
  {
    .get instance object modopt(uint16) A::GetProperty2()
    .set instance void modreq(System.Runtime.CompilerServices.IsExternalInit) A::SetProperty2(object modopt(uint16))
  }
  .method family virtual instance class [mscorlib]System.Type GetProperty1() { ldnull ret }
  .method public abstract virtual instance object modopt(uint16) GetProperty2() { }
  .method public abstract virtual instance void modreq(System.Runtime.CompilerServices.IsExternalInit) SetProperty2(object modopt(uint16) 'value') { }
  .method public newslot virtual instance bool Equals(class A '') { ldnull throw }
  .method family hidebysig newslot virtual instance bool PrintMembers(class [mscorlib]System.Text.StringBuilder builder) { ldnull throw }
}
"#,
        r#"
record B(object P) : A
{
    static void Main()
    {
        B b = new B(3);
        System.Console.WriteLine(b.P);
        System.Console.WriteLine(((A)b).P);
        b = new B(1) { P = 2 };
        System.Console.WriteLine(b.P);
    }
}
"#,
        "3\n3\n2\n",
    );
}

#[test]
fn an_async_method_returns_a_task_like_type_another_assembly_declares() {
    // UniTask's shape: a struct names its builder with `[AsyncMethodBuilder]`,
    // and the method returning it is compiled against the assembly rather
    // than beside its source, so the builder has to be read off metadata.
    check_with_library(
        "TaskLikeAcross",
        r#"
using System;
using System.Runtime.CompilerServices;
using System.Threading.Tasks;

namespace Lib
{
    [AsyncMethodBuilder(typeof(MyTaskBuilder))]
    public readonly struct MyTask
    {
        private readonly Task task;
        public MyTask(Task task) { this.task = task; }
        public TaskAwaiter GetAwaiter() => task.GetAwaiter();
    }

    [AsyncMethodBuilder(typeof(MyTaskBuilder<>))]
    public readonly struct MyTask<T>
    {
        private readonly Task<T> task;
        public MyTask(Task<T> task) { this.task = task; }
        public TaskAwaiter<T> GetAwaiter() => task.GetAwaiter();
    }

    public struct MyTaskBuilder
    {
        private AsyncTaskMethodBuilder inner;
        public static MyTaskBuilder Create()
        {
            Console.Write("[made]");
            return new MyTaskBuilder { inner = AsyncTaskMethodBuilder.Create() };
        }
        public void Start<TStateMachine>(ref TStateMachine stateMachine)
            where TStateMachine : IAsyncStateMachine => inner.Start(ref stateMachine);
        public void SetStateMachine(IAsyncStateMachine stateMachine) => inner.SetStateMachine(stateMachine);
        public void SetException(Exception exception) => inner.SetException(exception);
        public void SetResult() => inner.SetResult();
        public void AwaitOnCompleted<TAwaiter, TStateMachine>(ref TAwaiter awaiter, ref TStateMachine stateMachine)
            where TAwaiter : INotifyCompletion
            where TStateMachine : IAsyncStateMachine => inner.AwaitOnCompleted(ref awaiter, ref stateMachine);
        public void AwaitUnsafeOnCompleted<TAwaiter, TStateMachine>(ref TAwaiter awaiter, ref TStateMachine stateMachine)
            where TAwaiter : ICriticalNotifyCompletion
            where TStateMachine : IAsyncStateMachine => inner.AwaitUnsafeOnCompleted(ref awaiter, ref stateMachine);
        public MyTask Task => new MyTask(inner.Task);
    }

    public struct MyTaskBuilder<T>
    {
        private AsyncTaskMethodBuilder<T> inner;
        public static MyTaskBuilder<T> Create()
        {
            Console.Write("[made<T>]");
            return new MyTaskBuilder<T> { inner = AsyncTaskMethodBuilder<T>.Create() };
        }
        public void Start<TStateMachine>(ref TStateMachine stateMachine)
            where TStateMachine : IAsyncStateMachine => inner.Start(ref stateMachine);
        public void SetStateMachine(IAsyncStateMachine stateMachine) => inner.SetStateMachine(stateMachine);
        public void SetException(Exception exception) => inner.SetException(exception);
        public void SetResult(T result) => inner.SetResult(result);
        public void AwaitOnCompleted<TAwaiter, TStateMachine>(ref TAwaiter awaiter, ref TStateMachine stateMachine)
            where TAwaiter : INotifyCompletion
            where TStateMachine : IAsyncStateMachine => inner.AwaitOnCompleted(ref awaiter, ref stateMachine);
        public void AwaitUnsafeOnCompleted<TAwaiter, TStateMachine>(ref TAwaiter awaiter, ref TStateMachine stateMachine)
            where TAwaiter : ICriticalNotifyCompletion
            where TStateMachine : IAsyncStateMachine => inner.AwaitUnsafeOnCompleted(ref awaiter, ref stateMachine);
        public MyTask<T> Task => new MyTask<T>(inner.Task);
    }
}
"#,
        r#"
using System;
using System.Threading.Tasks;
using Lib;

static class Program
{
    static async MyTask<int> Twice(int x)
    {
        await Task.Yield();
        return x * 2;
    }

    static async MyTask Say(string text)
    {
        await Task.Delay(1);
        Console.WriteLine(text);
    }

    static async Task Main()
    {
        Console.WriteLine(await Twice(21));
        await Say("done");
    }
}
"#,
        "[made<T>]42\n[made]done\n",
    );
}

#[test]
fn not_calls_the_bool_conversion_a_base_class_declares() {
    // `if (!animator)` on a `UnityEngine.Object`: the predefined `!(bool)`
    // takes the operand through the `operator bool` its base declares.
    check(
        "NotThroughConversion",
        r#"
class Base
{
    public bool alive = true;
    public static implicit operator bool(Base b) => b != null && b.alive;
}
class Derived : Base { }
static class Program
{
    static void Main()
    {
        Derived d = new Derived();
        System.Console.Write(!d ? "dead" : "alive");
        Derived n = null;
        System.Console.Write(!n ? " null-dead" : " null-alive");
        Base b = new Base { alive = false };
        if (!b) System.Console.Write(" b-dead");
        System.Console.WriteLine(d && !n ? " and" : " nand");
    }
}
"#,
        "alive null-dead b-dead and\n",
    );
}

#[test]
fn a_constant_given_to_an_in_parameter_is_held_in_a_slot() {
    // A constant has no storage: `ldsflda` of a literal field is a
    // `MissingFieldException` when the method is compiled.
    check(
        "ConstantToIn",
        r#"
enum Kind : byte { None = 0, Start = 2, Stop = 4 }
static class Consts { public const int Answer = 42; public const string Name = "n"; }
static class Program
{
    static void M(in Kind kind) => System.Console.Write((int)kind + " ");
    static void N(in int x) => System.Console.Write(x + " ");
    static void S(in string s) => System.Console.Write(s + " ");
    static void Main()
    {
        M(Kind.Stop);
        N(Consts.Answer);
        N(7);
        S(Consts.Name);
        System.Console.WriteLine();
    }
}
"#,
        "4 42 7 n \n",
    );
}

#[test]
fn a_generic_class_forwards_an_in_parameter_to_a_generic_interface() {
    // The interface's `in` is under `modreq(InAttribute)` and the class's
    // public method's is not: the runtime needs a private method with the
    // interface's signature, which in a generic class calls through `R<!0>`,
    // and an interface inherited through another is forwarded to once.
    check(
        "GenericInForwarder",
        r#"
using System.Collections.Generic;
public struct Env { public int X; }
public interface IIdx<T> { List<T> Search(in Env e); }
public interface IDb<T> : IIdx<T> { void Clear(); }
public class R<T> : IDb<T>
{
    public List<T> Search(in Env e) { System.Console.Write("found " + e.X + " "); return new List<T>(); }
    public void Clear() { }
}
static class Program
{
    static void Main()
    {
        IIdx<int> index = new R<int>();
        System.Console.WriteLine(index.Search(new Env { X = 5 }).Count);
        IDb<string> database = new R<string>();
        System.Console.WriteLine(database.Search(new Env { X = 6 }).Count);
    }
}
"#,
        "found 5 0\nfound 6 0\n",
    );
}

#[test]
fn operators_reach_a_struct_through_its_conversions_to_int() {
    // Unity's `LayerMask`: no `~`, `|` or `==` of its own, only conversions
    // to and from `int`, which the predefined operators go through.
    check(
        "MaskOperators",
        r#"
public struct Mask
{
    public int value;
    public static implicit operator int(Mask m) => m.value;
    public static implicit operator Mask(int v) => new Mask { value = v };
}
static class Masks
{
    public static readonly Mask A = 1 << 3;
    public static readonly Mask B = 1 << 5;
    public static readonly Mask Both = A | B;
    public static readonly Mask NotA = ~A;
    public static readonly Mask Some = -1 & ~A & ~B;
}
static class Program
{
    static void Main()
    {
        System.Console.WriteLine((int)Masks.Both + " " + (int)Masks.NotA + " " + (int)Masks.Some);
        Mask m = Masks.A;
        System.Console.WriteLine((m | Masks.B) == 40);
        System.Console.WriteLine(m == Masks.A);
        System.Console.WriteLine(m != Masks.B);
    }
}
"#,
        "40 -9 -41\nTrue\nTrue\nTrue\n",
    );
}

#[test]
fn a_compound_assignment_to_a_field_of_a_struct_variable_calls_the_operator() {
    // `placement.Position += offset` through a `ref` local, with the `+` a
    // referenced struct declares: a field of a variable is as cheap to read
    // twice as the variable.
    check(
        "CompoundThroughField",
        r#"
using System.Numerics;
struct Placement { public Vector2 Position; public float Angle; }
struct Mine { public int x; public static Mine operator +(Mine a, Mine b) => new Mine { x = a.x + b.x }; }
struct Holder { public Mine M; }
static class Program
{
    static Placement[] items = new Placement[1];
    static void Main()
    {
        ref var p = ref items[0];
        p.Position += new Vector2(1, 2) * 3f;
        p.Angle += 0.5f;
        var local = new Placement();
        local.Position += new Vector2(4, 5);
        var holders = new Holder[1];
        ref var h = ref holders[0];
        h.M += new Mine { x = 7 };
        System.Console.WriteLine($"{items[0].Position.X} {items[0].Position.Y} {items[0].Angle} {local.Position.X} {holders[0].M.x}");
    }
}
"#,
        "3 6 0.5 4 7\n",
    );
}

#[test]
fn an_async_lambda_picks_the_overload_taking_a_task_like_type_with_a_result() {
    // `UniTask.Create(async () => await Check(id))`: the lambda gives a
    // `MyTask<bool>` to `Create<T>(Func<MyTask<T>>)`, which infers `T` and
    // is the better of the two over `Create(Func<MyTask>)`.
    check_with_library(
        "TaskLikeOverloads",
        r#"
using System;
using System.Runtime.CompilerServices;
using System.Threading.Tasks;

namespace Lib
{
    [AsyncMethodBuilder(typeof(MyTaskBuilder))]
    public readonly struct MyTask
    {
        private readonly Task task;
        public MyTask(Task task) { this.task = task; }
        public TaskAwaiter GetAwaiter() => task.GetAwaiter();
    }

    [AsyncMethodBuilder(typeof(MyTaskBuilder<>))]
    public readonly struct MyTask<T>
    {
        private readonly Task<T> task;
        public MyTask(Task<T> task) { this.task = task; }
        public TaskAwaiter<T> GetAwaiter() => task.GetAwaiter();
    }

    public static class Tasks
    {
        public static MyTask Create(Func<MyTask> factory) => factory();
        public static MyTask<T> Create<T>(Func<MyTask<T>> factory) => factory();
    }

    public struct MyTaskBuilder
    {
        private AsyncTaskMethodBuilder inner;
        public static MyTaskBuilder Create()
        {
            Console.Write("[made]");
            return new MyTaskBuilder { inner = AsyncTaskMethodBuilder.Create() };
        }
        public void Start<TStateMachine>(ref TStateMachine stateMachine)
            where TStateMachine : IAsyncStateMachine => inner.Start(ref stateMachine);
        public void SetStateMachine(IAsyncStateMachine stateMachine) => inner.SetStateMachine(stateMachine);
        public void SetException(Exception exception) => inner.SetException(exception);
        public void SetResult() => inner.SetResult();
        public void AwaitOnCompleted<TAwaiter, TStateMachine>(ref TAwaiter awaiter, ref TStateMachine stateMachine)
            where TAwaiter : INotifyCompletion
            where TStateMachine : IAsyncStateMachine => inner.AwaitOnCompleted(ref awaiter, ref stateMachine);
        public void AwaitUnsafeOnCompleted<TAwaiter, TStateMachine>(ref TAwaiter awaiter, ref TStateMachine stateMachine)
            where TAwaiter : ICriticalNotifyCompletion
            where TStateMachine : IAsyncStateMachine => inner.AwaitUnsafeOnCompleted(ref awaiter, ref stateMachine);
        public MyTask Task => new MyTask(inner.Task);
    }

    public struct MyTaskBuilder<T>
    {
        private AsyncTaskMethodBuilder<T> inner;
        public static MyTaskBuilder<T> Create()
        {
            Console.Write("[made<T>]");
            return new MyTaskBuilder<T> { inner = AsyncTaskMethodBuilder<T>.Create() };
        }
        public void Start<TStateMachine>(ref TStateMachine stateMachine)
            where TStateMachine : IAsyncStateMachine => inner.Start(ref stateMachine);
        public void SetStateMachine(IAsyncStateMachine stateMachine) => inner.SetStateMachine(stateMachine);
        public void SetException(Exception exception) => inner.SetException(exception);
        public void SetResult(T result) => inner.SetResult(result);
        public void AwaitOnCompleted<TAwaiter, TStateMachine>(ref TAwaiter awaiter, ref TStateMachine stateMachine)
            where TAwaiter : INotifyCompletion
            where TStateMachine : IAsyncStateMachine => inner.AwaitOnCompleted(ref awaiter, ref stateMachine);
        public void AwaitUnsafeOnCompleted<TAwaiter, TStateMachine>(ref TAwaiter awaiter, ref TStateMachine stateMachine)
            where TAwaiter : ICriticalNotifyCompletion
            where TStateMachine : IAsyncStateMachine => inner.AwaitUnsafeOnCompleted(ref awaiter, ref stateMachine);
        public MyTask<T> Task => new MyTask<T>(inner.Task);
    }
}
"#,
        r#"
using System;
using System.Threading.Tasks;
using Lib;
static class Program
{
    static async MyTask<bool> Check(string id) { await Task.Yield(); return id.Length > 2; }
    static async Task Main()
    {
        var id = "abcd";
        MyTask<bool> task = Tasks.Create(async () => await Check(id));
        Console.WriteLine(await task);
        MyTask plain = Tasks.Create(async () => { await Task.Yield(); Console.Write("plain "); });
        await plain;
        Console.WriteLine();
    }
}
"#,
        "[made<T>][made<T>]True\n[made]plain \n",
    );
}

#[test]
fn a_compound_assignment_to_a_property_goes_through_the_struct_conversions() {
    // `collider.includeLayers |= mask` on Unity's `LayerMask`: a property
    // is read and written once each, its receiver evaluated once, and the
    // `|` is the one on `int` the conversions reach.
    check(
        "CompoundPropertyThroughConversions",
        r#"
public struct Mask
{
    public int value;
    public static implicit operator int(Mask m) => m.value;
    public static implicit operator Mask(int v) => new Mask { value = v };
}
class Collider { public Mask includeLayers { get; set; } public Mask excludeLayers { get; set; } = -1; }
static class Program
{
    static int reads;
    static Collider Get(Collider c) { reads++; return c; }
    static void Main()
    {
        var c = new Collider();
        Mask m = 1 << 4;
        c.includeLayers |= m;
        c.excludeLayers &= ~m;
        Get(c).includeLayers |= 1 << 1;
        System.Console.WriteLine((int)c.includeLayers + " " + (int)c.excludeLayers + " " + reads);
    }
}
"#,
        "18 -17 1\n",
    );
}

#[test]
fn internals_are_seen_by_the_assembly_a_reference_names_its_friend() {
    // An editor's hot patch reaches the game's internal members because the
    // game names the patch in an `[InternalsVisibleTo]`; anyone else does not
    // see them at all.
    let Some(mut bytes) = references() else {
        println!("note: the friend test was skipped; no .NET shared framework was found");
        return;
    };
    let library = r#"
[assembly: System.Runtime.CompilerServices.InternalsVisibleTo("Friend")]
internal class Hidden
{
    internal int secret = 41;
    internal static string Name => "hidden";
}
"#;
    let directory = scratch("Friend");
    let compilation = compiled("FriendLibrary", library, &bytes);
    let emitted = rustlyn_emit::emit_library(&compilation, "FriendLibrary")
        .unwrap_or_else(|error| panic!("FriendLibrary could not be emitted: {error}"));
    std::fs::write(directory.join("FriendLibrary.dll"), &emitted.assembly)
        .expect("the library should be writable");
    bytes.push(emitted.assembly);
    let program = r#"
static class Program
{
    static void Main() => System.Console.WriteLine(Hidden.Name + " " + (new Hidden().secret + 1));
}
"#;
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
    let stranger = Compilation::create_with_references(
        vec![parse(SourceText::new("Program.cs", program))],
        &images,
    );
    assert!(
        !stranger.semantic_diagnostics().is_empty(),
        "an assembly the library does not name should not see its internals"
    );
    let friend = Compilation::create_with_references_as(
        vec![parse(SourceText::new("Program.cs", program))],
        &images,
        "Friend",
    );
    let diagnostics: Vec<String> = friend
        .semantic_diagnostics()
        .iter()
        .map(|entry| friend.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    let emitted = rustlyn_emit::emit(&friend, "Friend")
        .unwrap_or_else(|error| panic!("Friend could not be emitted: {error}"));
    run_emitted("Friend", &directory, &emitted, "hidden 42\n");
}

#[test]
fn a_type_two_references_both_declare_is_ambiguous() {
    // An editor's hot patch compiled against a game assembly built from
    // older sources, and against today's assemblies that some of its types
    // have since moved to: a name finds both, and which one it meant cannot
    // be told (CS0433). Taking either made the other's methods refuse it,
    // with a message naming the same type twice.
    let Some(mut bytes) = references() else {
        println!("note: the ambiguity test was skipped; no .NET shared framework was found");
        return;
    };
    let game = r#"
namespace Game { public enum TimeFormat { Long, Symbols } public static class Clock { public static int Show(TimeFormat format) => (int)format; } }
"#;
    let moved = "namespace Game { public enum TimeFormat { Long, Symbols } }";
    for (name, source) in [("Game", game), ("Moved", moved)] {
        let compilation = compiled(name, source, &bytes);
        let emitted = rustlyn_emit::emit_library(&compilation, name)
            .unwrap_or_else(|error| panic!("{name} could not be emitted: {error}"));
        bytes.push(emitted.assembly);
    }
    let program = r#"
static class Program
{
    static int Expression() => Game.Clock.Show(global::Game.TimeFormat.Symbols);
    static void Local() { Game.TimeFormat format = default; }
}
"#;
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
    let compilation = Compilation::create_with_references(
        vec![parse(SourceText::new("Program.cs", program))],
        &images,
    );
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| compilation.render(entry))
        .collect();
    assert_eq!(
        diagnostics,
        [
            "Program.cs(4,61): error CS0433: The type 'TimeFormat' exists in both 'Game, Version=0.0.0.0' and 'Moved, Version=0.0.0.0'",
            "Program.cs(5,32): error CS0433: The type 'TimeFormat' exists in both 'Game, Version=0.0.0.0' and 'Moved, Version=0.0.0.0'",
        ],
    );
}

#[test]
fn an_event_implements_an_interface_event_of_a_reference() {
    // `class Model : INotifyPropertyChanged { public event
    // PropertyChangedEventHandler PropertyChanged; }`: the interface's
    // `add_` and `remove_` are its event's, and were read as methods of
    // their own too, which nothing in the class implemented (CS0535).
    check(
        "InterfaceEvent",
        r#"
using System;
using System.ComponentModel;
class Model : INotifyPropertyChanged
{
    public event PropertyChangedEventHandler PropertyChanged;
    public void Change(string name) => PropertyChanged?.Invoke(this, new PropertyChangedEventArgs(name));
}
static class Program
{
    static void Main()
    {
        var model = new Model();
        INotifyPropertyChanged seen = model;
        PropertyChangedEventHandler handler = (sender, e) => Console.WriteLine("changed " + e.PropertyName);
        seen.PropertyChanged += handler;
        model.Change("Name");
        seen.PropertyChanged -= handler;
        model.Change("Age");
        Console.WriteLine("done");
    }
}
"#,
        "changed Name\ndone\n",
    );
}

#[test]
fn a_layout_written_with_constant_expressions_is_kept() {
    // `[StructLayout(LayoutKind.Explicit, Size = 4 * sizeof(byte))]` and a
    // `[FieldOffset(Offsets.Second)]` were read as written text, a literal
    // or nothing: the size was dropped, and the field given no offset made
    // the type fail to load. A layout on a later part of a partial struct
    // counts as well.
    check(
        "ConstantLayout",
        r#"
using System;
using System.Runtime.InteropServices;
static class Offsets { public const int Second = 4; }
[StructLayout(LayoutKind.Explicit, Size = 4 * sizeof(int), Pack = 1 + 1)]
struct Wide { [FieldOffset(0)] public int A; [FieldOffset(Offsets.Second)] public int B; [FieldOffset(Offsets.Second)] public float Same; }
[StructLayout(LayoutKind.Sequential, Size = 3)] struct Small { public byte X; }
partial struct Later { public byte Y; }
[StructLayout(LayoutKind.Sequential, Size = 7)] partial struct Later { }
unsafe static class Program
{
    static void Main()
    {
        var wide = new Wide { B = 1 };
        Console.WriteLine(sizeof(Wide) + " " + sizeof(Small) + " " + sizeof(Later) + " " + (wide.Same != 0));
    }
}
"#,
        "16 3 7 True\n",
    );
}

#[test]
fn the_field_of_a_field_like_event_is_private() {
    // As Roslyn makes it: a public delegate field is one that serializers
    // reading public fields — Odin's, Json.NET's — pick up. Inside the type,
    // a type nested in it and a lambda use the event as its field; anywhere
    // else `+=` calls the accessor.
    check(
        "PrivateEventField",
        r#"
using System;
using System.Reflection;
class Source
{
    public event Action<string> Changed;
    public static event Action Ticked;
    public void Raise(string what) { Action later = () => Changed?.Invoke(what); later(); }
    public class Inner { public void Raise(Source source) => source.Changed?.Invoke("inner"); }
    public static void Tick() => Ticked?.Invoke();
}
class Derived : Source { public Derived() { Changed += what => Console.WriteLine("derived " + what); } }
static class Program
{
    static void Main()
    {
        var source = new Derived();
        source.Changed += what => Console.WriteLine("seen " + what);
        Source.Ticked += () => Console.WriteLine("tick");
        source.Raise("a");
        new Source.Inner().Raise(source);
        Source.Tick();
        var field = typeof(Source).GetField("Changed", BindingFlags.Instance | BindingFlags.NonPublic | BindingFlags.Public);
        var ticked = typeof(Source).GetField("Ticked", BindingFlags.Static | BindingFlags.NonPublic | BindingFlags.Public);
        Console.WriteLine(field.IsPrivate + " " + ticked.IsPrivate);
    }
}
"#,
        "derived a\nseen a\nderived inner\nseen inner\ntick\nTrue True\n",
    );
}

#[test]
fn an_array_of_constants_is_copied_out_of_the_image() {
    // `RuntimeHelpers.InitializeArray` over a field of
    // `<PrivateImplementationDetails>` whose bytes are in the image, as
    // Roslyn does it: Unity's generated `AssemblyMonoScriptTypes` holds two
    // arrays of two million bytes, which an instruction per element made a
    // method of thirty-six megabytes. Blobs of one, two, four and eight
    // bytes are typed as the integer of that size, a blob two arrays share
    // is one field, and fewer than three elements other than zero, or one
    // that is not a constant, are still stored one by one.
    let mut big = String::from("new byte[] {");
    for at in 0..5000 {
        big.push_str(&format!("{}, ", (at * 7) % 256));
    }
    big.push('}');
    let source = r#"
using System;
using System.Linq;
using System.Reflection;
static class Program
{
    static readonly byte[] Bytes = { 1, 2, 3, 0, 255, 7 };
    static readonly int[] Ints = new int[5] { -1, 2, 0, 400000, 5 };
    static readonly double[] Doubles = { 1.5, -2, 0, 3 };
    static readonly float[] Floats = { 1, 2.5f, 3 };
    static readonly char[] Chars = { 'a', 'b', 'c', '\0' };
    static readonly bool[] Flags = { true, false, true, true };
    static readonly long[] Longs = { long.MaxValue, 1, 2 };
    static readonly ushort[] Shorts = { 1, 2, 3, 65535 };
    static readonly int[] Two = { 1, 2 };
    static readonly object[] Objects = { 0, false, null, 'x' };
    static readonly byte[] Big = BIG;
    static int Next(ref int at) => ++at;
    static void Main()
    {
        Console.WriteLine(string.Join(",", Bytes) + " " + string.Join(",", Ints) + " " + string.Join(",", Doubles) + " " + string.Join(",", Floats));
        Console.WriteLine(new string(Chars, 0, 3) + " " + string.Join(",", Flags) + " " + string.Join(",", Longs) + " " + string.Join(",", Shorts) + " " + string.Join(",", Two));
        Console.WriteLine((Objects[0] ?? "null") + " " + (Objects[1] ?? "null") + " " + (Objects[2] ?? "null") + " " + Objects[3]);
        var again = new byte[] { 1, 2, 3, 0, 255, 7 };
        int at = 0;
        var mixed = new[] { 5, Next(ref at), 7, 8 };
        Console.WriteLine(again.Length + " " + again[4] + " " + string.Join(",", mixed) + " " + Big.Length + " " + Big[4999] + " " + Big.Sum(b => (int)b));
        var details = typeof(Program).Assembly.GetType("<PrivateImplementationDetails>");
        var fields = details.GetFields(BindingFlags.NonPublic | BindingFlags.Static);
        Console.WriteLine(fields.Length + " " + string.Join(",", fields.Select(f => f.FieldType.Name).OrderBy(n => n, StringComparer.Ordinal)));
    }
}
"#
    .replace("BIG", &big);
    let sum: u32 = (0..5000).map(|at| (at * 7) % 256).sum();
    check(
        "ArrayData",
        &source,
        &format!(
            "1,2,3,0,255,7 -1,2,0,400000,5 1.5,-2,0,3 1,2.5,3\nabc True,False,True,True 9223372036854775807,1,2 1,2,3,65535 1,2\n0 False null x\n6 255 5,1,7,8 5000 {} {sum}\n9 Int32,Int64,Int64,__StaticArrayInitTypeSize=12,__StaticArrayInitTypeSize=20,__StaticArrayInitTypeSize=24,__StaticArrayInitTypeSize=32,__StaticArrayInitTypeSize=5000,__StaticArrayInitTypeSize=6\n",
            (4999 * 7) % 256
        ),
    );
}

#[test]
fn a_struct_with_no_instance_field_says_it_is_one_byte() {
    // As Roslyn writes it, where no `[StructLayout]` says otherwise: the tag
    // components of an ECS are thousands of such structs.
    check(
        "EmptyStructLayout",
        r#"
using System;
using System.Runtime.InteropServices;
struct Tag { }
struct OnlyStatic { public static int Count; }
[StructLayout(LayoutKind.Sequential)] struct Said { }
struct Full { public int X; }
record struct Point;
static class Program
{
    static void Main()
    {
        foreach (var type in new[] { typeof(Tag), typeof(OnlyStatic), typeof(Said), typeof(Full), typeof(Point) })
            Console.Write(type.StructLayoutAttribute.Size + " ");
        Console.WriteLine();
    }
}
"#,
        "1 1 0 0 1 \n",
    );
}

/// A lambda in an async method that is generic captures locals into a
/// display class generic over the method's type parameters. In the state
/// machine those are the machine's own type parameters: the class is made
/// over the machine's (`!0`), not the method's (`!!0`), which `MoveNext`
/// does not have — Mono's JIT asserts on that, CoreCLR rejects it.
#[test]
fn a_lambda_in_a_generic_async_method_captures_through_the_machine() {
    check(
        "GenericAsyncLambda",
        r#"
using System;
using System.Threading.Tasks;
class GenericAsyncLambda
{
    static bool Next(string[] items, ref int index, out string item)
    {
        item = index < items.Length ? items[index] : null;
        index++;
        return item != null;
    }

    static async Task<string> Go<T>(T value) where T : class
    {
        var items = new[] { "x", "y" };
        var index = 0;
        var collected = "";
        while (Next(items, ref index, out var item))
        {
            var full = item + value;
            Func<string> describe = () => collected + full + item;
            await Task.Yield();
            collected = describe();
        }
        return collected;
    }

    static void Main()
    {
        Console.WriteLine(Go<string>("v").Result);
    }
}
"#,
        "xvxyvy\n",
    );
}

/// `[field: A]` on an automatic property goes on the field the property
/// keeps its value in, and only there: Unity serializes such a property by
/// `[field: SerializeField]`, and a build without it on the field reads
/// back what another build wrote of the object past its end.
#[test]
fn a_field_attribute_on_an_automatic_property_is_its_fields() {
    check(
        "PropertyField",
        r#"
using System;
using System.Reflection;
[AttributeUsage(AttributeTargets.Field | AttributeTargets.Property)]
class Marker : Attribute { }
class Holder
{
    [field: Marker] public int Kept { get; private set; }
    [Marker] public int Plain { get; set; }
}
class PropertyField
{
    static void Main()
    {
        var flags = BindingFlags.NonPublic | BindingFlags.Instance;
        var kept = typeof(Holder).GetField("<Kept>k__BackingField", flags);
        var plain = typeof(Holder).GetField("<Plain>k__BackingField", flags);
        Console.WriteLine(kept.IsDefined(typeof(Marker)));
        Console.WriteLine(typeof(Holder).GetProperty("Kept").IsDefined(typeof(Marker)));
        Console.WriteLine(plain.IsDefined(typeof(Marker)));
        Console.WriteLine(typeof(Holder).GetProperty("Plain").IsDefined(typeof(Marker)));
    }
}
"#,
        "True\nFalse\nFalse\nTrue\n",
    );
}

/// An editor's build drops `initonly` so that a patch can set a field from
/// outside its constructor — but not from the fields of what Unity
/// serializes: an editor reloading reads back the fields it wrote, as csc's
/// build has them.
#[test]
fn an_editors_build_keeps_initonly_on_a_serializable_types_fields() {
    let name = "WidenKeepsSerializedReadonly";
    let Some(bytes) = references() else {
        println!("note: {name} was skipped; no .NET shared framework was found");
        return;
    };
    let source = r#"
using System;
using System.Reflection;

[Serializable]
class Saved { readonly int kept = 1; public int Get() => kept; }

class Plain { readonly int dropped = 2; public int Get() => dropped; }

static class Shared { static readonly int alsoDropped = 3; public static int Get() => alsoDropped; }

class Program
{
    static void Main()
    {
        var all = BindingFlags.Instance | BindingFlags.Static | BindingFlags.NonPublic | BindingFlags.Public;
        Console.WriteLine(typeof(Saved).GetField("kept", all).IsInitOnly);
        Console.WriteLine(typeof(Plain).GetField("dropped", all).IsInitOnly);
        Console.WriteLine(typeof(Shared).GetField("alsoDropped", all).IsInitOnly);
        Console.WriteLine(new Saved().Get() + new Plain().Get() + Shared.Get());
    }
}
"#;
    let compilation = compiled(name, source, &bytes);
    let (_, emitted, _) = rustlyn_emit::incremental_with(
        &compilation,
        name,
        rustlyn_emit::IncrementalOptions {
            widen_for_patches: true,
            ..Default::default()
        },
    )
    .unwrap_or_else(|error| panic!("{name} could not be emitted: {error}"));
    run_emitted(name, &scratch(name), &emitted, "True\nFalse\nFalse\n6\n");
}

/// An editor's build gives a getter-only automatic property an internal
/// setter of its backing field, so that a patched constructor — a static
/// method of another assembly — can still set it; a property something
/// overrides keeps what it declared.
#[test]
fn an_editors_build_opens_a_setter_on_a_getter_only_property() {
    let name = "WidenOpensGetterOnlySetter";
    let Some(bytes) = references() else {
        println!("note: {name} was skipped; no .NET shared framework was found");
        return;
    };
    let source = r#"
using System;
using System.Reflection;

class Model
{
    public int Count { get; }
    public static string Name { get; } = "start";
    public virtual int Kind { get; }
    public Model(int count) { Count = count; }
}

class Program
{
    static void Main()
    {
        var all = BindingFlags.Instance | BindingFlags.Static | BindingFlags.NonPublic | BindingFlags.Public;
        var model = new Model(4);
        Console.WriteLine(model.Count);
        var count = typeof(Model).GetProperty("Count", all).GetSetMethod(true);
        Console.WriteLine(count != null && count.IsAssembly);
        count.Invoke(model, new object[] { 7 });
        Console.WriteLine(model.Count);
        typeof(Model).GetProperty("Name", all).GetSetMethod(true).Invoke(null, new object[] { "patched" });
        Console.WriteLine(Model.Name);
        Console.WriteLine(typeof(Model).GetProperty("Kind", all).GetSetMethod(true) == null);
    }
}
"#;
    let compilation = compiled(name, source, &bytes);
    let (_, emitted, _) = rustlyn_emit::incremental_with(
        &compilation,
        name,
        rustlyn_emit::IncrementalOptions {
            widen_for_patches: true,
            ..Default::default()
        },
    )
    .unwrap_or_else(|error| panic!("{name} could not be emitted: {error}"));
    run_emitted(
        name,
        &scratch(name),
        &emitted,
        "4\nTrue\n7\npatched\nTrue\n",
    );
}

#[test]
fn an_unchecked_narrowing_of_a_constant_wraps_to_the_narrower_type() {
    // Folded at compile time: `unchecked((byte)-1)` is the byte 255, not the
    // int -1 it was written as, and a `char` keeps 16 bits. A floating
    // constant its target has no room for — `unchecked((byte)300.7)` — is
    // zero, as Roslyn folds it.
    check(
        "ConstantNarrowing",
        r#"using System;
class P {
    const byte B = unchecked((byte)(-1));
    static void Main() {
        Console.WriteLine(unchecked((byte)(-1)) + 0);
        Console.WriteLine(unchecked((ushort)(-1)) + 0);
        Console.WriteLine(unchecked((sbyte)200) + 0);
        Console.WriteLine(unchecked((short)40000) + 0);
        Console.WriteLine(B + 0);
        byte b = 5; Console.WriteLine(b + 1);
        Console.WriteLine((char)65);
        Console.WriteLine(unchecked((char)(-1)) + 0);
        Console.WriteLine(unchecked((char)0xD800) + 0);
        Console.WriteLine((int)1.9 + " " + (int)(-1.9) + " " + (long)2.5f);
        Console.WriteLine(unchecked((byte)300.7) + 0);
        Console.WriteLine((uint)(-1.0 + 2) + " " + unchecked((sbyte)(byte)255) );
        Console.WriteLine(unchecked((byte)ulong.MaxValue) + 0);
        Console.WriteLine(unchecked((int)ulong.MaxValue));
        Console.WriteLine(unchecked((long)ulong.MaxValue));
        Console.WriteLine('a' + 1);
        Console.WriteLine((char)('a' + 1));
    }
}
"#,
        "255
65535
-56
-25536
255
6
A
65535
55296
1 -1 2
0
1 -1
255
-1
-1
98
b
",
    );
}

#[test]
fn a_handler_argument_named_with_nameof_reaches_the_handler() {
    // Roslyn's own `RoslynDebug.Assert` names its condition `nameof(condition)`.
    check(
        "HandlerNameof",
        r#"
using System;
using System.Runtime.CompilerServices;
static class D
{
    public static void Assert(bool condition, [InterpolatedStringHandlerArgument(nameof(condition))] ref H message)
    {
        Console.WriteLine(condition ? "fine" : message.Text);
    }
    [InterpolatedStringHandler]
    public ref struct H
    {
        public string Text;
        public H(int literalLength, int formattedCount, bool condition, out bool shouldAppend)
        {
            Text = "";
            shouldAppend = !condition;
        }
        public void AppendLiteral(string s) => Text += s;
        public void AppendFormatted<T>(T t) => Text += t;
    }
    static void Main()
    {
        int built = 0;
        Assert(true, $"never {built++}");
        Assert(false, $"bad {built++}");
        Console.WriteLine(built);
    }
}
"#,
        "fine\nbad 0\n1\n",
    );
}

#[test]
fn an_interface_operator_is_implemented_explicitly() {
    // `static C IAdd<C>.operator +(…)` (C# 11): an explicit implementation
    // of a static abstract operator, which did not parse.
    check(
        "ExplicitInterfaceOperator",
        r#"using System;
interface IAdd<T> where T : IAdd<T> { static abstract T operator +(T a, T b); }
struct C : IAdd<C>
{
    public int V;
    static C IAdd<C>.operator +(C a, C b) => new C { V = a.V + b.V };
}
static class P
{
    static T Sum<T>(T a, T b) where T : IAdd<T> => a + b;
    static void Main() { Console.WriteLine(Sum(new C { V = 2 }, new C { V = 3 }).V); }
}
"#,
        "5\n",
    );
}

#[test]
fn a_type_parameter_converts_through_its_constraints_operator() {
    // `(int)value` on a `T : IConv<T>` calls the static abstract
    // `op_Explicit` the constraint declares (C# 11); it was a `conv.i4` of
    // the value, which printed the struct's first field.
    check(
        "ConstraintConversion",
        r#"using System;
interface IConv<T> where T : IConv<T> { static abstract explicit operator int(T c); }
struct C : IConv<C>
{
    public int V;
    static explicit IConv<C>.operator int(C c) => c.V * 10;
}
static class P
{
    static int Of<T>(T value) where T : IConv<T> => (int)value;
    static void Main() { Console.WriteLine(Of(new C { V = 4 })); }
}
"#,
        "40\n",
    );
}

#[test]
fn a_type_parameter_and_a_value_type_convert_through_a_box() {
    // `(int)t` is `box !!T; unbox.any int32`: it throws where `T` is no
    // `int`, where a number conversion read a reference as its address.
    check(
        "TypeParameterUnbox",
        r#"static class Q { static int F<T>(T v) => (int)v; static T G<T>(int i) => (T)i; static void Main() { System.Console.WriteLine(F(3) + " " + G<int>(4)); try { F<object>("x"); } catch (System.InvalidCastException) { System.Console.WriteLine("cast"); } } }
"#,
        "3 4\ncast\n",
    );
}

/// `null` beside a struct that takes it through an operator of its own is
/// that struct, not its nullable: `n > 2 ? new ArraySegment<byte>(…) : null`
/// is an `ArraySegment<byte>`, the null made by its operator from `byte[]`.
#[test]
fn a_conditional_of_a_struct_and_null_is_the_struct_its_operator_makes() {
    check(
        "ConditionalNullOperator",
        r#"
using System;

class Program
{
    static ArraySegment<byte> Data;

    static void Main()
    {
        var bytes = new byte[] { 1, 2, 3, 4 };
        foreach (var n in new[] { 4, 1 })
        {
            Data = n > 2 ? new ArraySegment<byte>(bytes, 1, 2) : null;
            Console.WriteLine(Data.Count + " " + (Data.Array == null));
        }
    }
}
"#,
        "2 False\n0 True\n",
    );
}

/// A method group none of whose methods takes what a delegate hands it
/// infers nothing: `Select(Create)` over results is not LINQ's `(T, int)`
/// overload because one `Create` has two parameters, and the result is
/// what `Create(ITestResult)` returns.
#[test]
fn a_group_infers_nothing_from_a_delegate_none_of_its_methods_takes() {
    check(
        "GroupInference",
        r#"
using System;
using System.Collections.Generic;
using System.Linq;

interface ITest { }
interface ITestResult { IEnumerable<ITestResult> Children { get; } }
interface ITestAdaptor { }
interface ITestResultAdaptor { }

class TestAdaptor : ITestAdaptor { }
class ResultAdaptor : ITestResultAdaptor { public ITestResultAdaptor[] Children; }
class Result : ITestResult { public IEnumerable<ITestResult> Children => new ITestResult[] { new Leaf() }; }
class Leaf : ITestResult { public IEnumerable<ITestResult> Children => new ITestResult[0]; }

class Factory
{
    public ITestAdaptor Create(ITest test) => new TestAdaptor();
    public ITestResultAdaptor Create(ITestResult result) =>
        new ResultAdaptor { Children = result.Children.Select(Create).ToArray() };
    public ITestAdaptor Create(ITest test, string filter) => Create(test);
}

class Program
{
    static void Main() => Console.WriteLine(((ResultAdaptor)new Factory().Create(new Result())).Children.Length);
}
"#,
        "1\n",
    );
}

/// Extension methods are looked for scope by scope, and a scope whose
/// candidates no lambda here fits is passed over: UniTask's
/// `Select(Func<T, UniTask>)` in an enclosing namespace does not take a
/// lambda giving a `string`, and LINQ's `Select` does.
#[test]
fn a_nearer_extension_no_lambda_fits_gives_way_to_a_farther_one() {
    check(
        "ExtensionScopes",
        r#"
using System;
using System.Collections.Generic;
using System.Linq;

namespace Tasks
{
    public struct UniTask { }

    public static class EnumerableAsyncExtensions
    {
        public static IEnumerable<UniTask> Select<T>(this IEnumerable<T> source, Func<T, UniTask> selector) => null;
    }
}

namespace Tasks.Internal
{
    static class Program
    {
        static string Name(int x) => "n" + x;

        static void Main()
        {
            var items = new[] { 1, 2 };
            Console.WriteLine(string.Join(", ", items.Select(p => Name(p) + " " + p)));
        }
    }
}
"#,
        "n1 1, n2 2\n",
    );
}

/// An explicit implementation of a generic interface method writes no
/// constraints and has the interface method's: `TList` is the
/// `IList<TElement>` the interface says, so it clears, adds and indexes.
#[test]
fn an_explicit_implementation_has_its_interface_methods_constraints() {
    check(
        "ExplicitConstraints",
        r#"
using System;
using System.Collections.Generic;

interface IVisitor
{
    void Visit<TList, TElement>(ref TList container, TElement element) where TList : IList<TElement>;
}

class Visitor : IVisitor
{
    void IVisitor.Visit<TList, TElement>(ref TList container, TElement element)
    {
        container.Clear();
        container.Add(element);
        container[0] = element;
        Console.WriteLine(container.Count + " " + container[0]);
    }
}

class Program
{
    static void Main()
    {
        var list = new List<int> { 1, 2 };
        ((IVisitor)new Visitor()).Visit<List<int>, int>(ref list, 7);
    }
}
"#,
        "1 7\n",
    );
}

#[test]
fn an_obsolete_member_of_a_reference_is_warned_about() {
    // Unity's `EditorGUILayout.ObjectField` without `allowSceneObjects` is
    // `[Obsolete("...")]`: a use of it is CS0618 with the message, a bare
    // `[Obsolete]` is CS0612, and `[Obsolete("...", true)]` is CS0619. Code
    // that is obsolete itself may use them; one with a `DiagnosticId` is
    // reported under that id by Roslyn, which is not done here. The marker
    // a `ref struct` carries against old compilers (`Span<T>`) is none.
    let Some(mut bytes) = references() else {
        println!("note: the obsolete test was skipped; no .NET shared framework was found");
        return;
    };
    let library = r#"
namespace Engine
{
    [System.Obsolete] public class OldType { }
    [System.Obsolete("Use UiObject instead")] public class UiInstance<T> { }
    [System.Obsolete("Use Widget instead")] public class OldBase { }
    public class StashAttribute : System.Attribute { public StashAttribute(System.Type type) { } }
    [System.Obsolete("Use systems instead")] public class LocalEventAttribute : System.Attribute { public LocalEventAttribute(string name) { } }
    public class Popup { [System.Obsolete("Use Show.")] public Popup(string title) { } public Popup() { } }
    public enum Flags { A = 1, [System.Obsolete("Navigation is gone.")] Navigation = 2 }
    public class DrawerAttribute : System.Attribute { [System.Obsolete("Use ShowFoldout.")] public bool Expanded { get; set; } public bool Draggable { get; set; } }
    public static class Gui
    {
        [System.Obsolete("Check the docs for allowSceneObjects.")] public static int Field(string label) => 0;
        [System.Obsolete("Gone.", true)] public static int Removed() => 0;
        [System.Obsolete("Use Next.", DiagnosticId = "ENG001")] public static int Tagged() => 0;
        public static int Current(string label) => 0;
    }
}
"#;
    let compilation = compiled("Engine", library, &bytes);
    let emitted = rustlyn_emit::emit_library(&compilation, "Engine")
        .unwrap_or_else(|error| panic!("Engine could not be emitted: {error}"));
    bytes.push(emitted.assembly);
    let program = r#"
using Engine;
static class Program
{
    static int Use() => Gui.Field("a") + Gui.Current("b") + Gui.Tagged();
    static OldType Make() => null;
    static int Gone() => Gui.Removed();
    static System.ReadOnlySpan<char> Span(string text) => System.MemoryExtensions.AsSpan(text);
    [System.Obsolete] static int Quiet() => Gui.Field("c");
}
[Stash(typeof(OldType))]
class Screen : OldBase
{
    System.Collections.Generic.List<UiInstance<Screen>> items;
}
[System.Obsolete]
class Retired : OldBase { OldType kept; }
class Events
{
    [LocalEvent("reached")] void Reached() { }
    object list = new System.Collections.Generic.List<OldType>();
    object popup = new Popup("title");
    const Flags All = Flags.A |
        Flags.Navigation;
    [Drawer(Expanded = true, Draggable = false)] int[] cells;
    string M()
    {
        OldType Local() => null;
        return nameof(UiInstance<Events>);
    }
}
"#;
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
    let compilation = Compilation::create_with_references(
        vec![parse(SourceText::new("Program.cs", program))],
        &images,
    );
    let mut diagnostics: Vec<(usize, String)> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| {
            (
                entry.diagnostic.span().start() as usize,
                compilation.render(entry),
            )
        })
        .collect();
    diagnostics.sort();
    let diagnostics: Vec<String> = diagnostics.into_iter().map(|(_, text)| text).collect();
    assert_eq!(
        diagnostics,
        [
            "Program.cs(5,25): warning CS0618: 'Gui.Field(string)' is obsolete: 'Check the docs for allowSceneObjects.'",
            "Program.cs(6,12): warning CS0612: 'OldType' is obsolete",
            "Program.cs(7,26): error CS0619: 'Gui.Removed()' is obsolete: 'Gone.'",
            "Program.cs(11,15): warning CS0612: 'OldType' is obsolete",
            "Program.cs(12,16): warning CS0618: 'OldBase' is obsolete: 'Use Widget instead'",
            "Program.cs(14,37): warning CS0618: 'UiInstance<Screen>' is obsolete: 'Use UiObject instead'",
            "Program.cs(20,6): warning CS0618: 'LocalEventAttribute' is obsolete: 'Use systems instead'",
            "Program.cs(21,55): warning CS0612: 'OldType' is obsolete",
            "Program.cs(22,20): warning CS0618: 'Popup.Popup(string)' is obsolete: 'Use Show.'",
            "Program.cs(24,9): warning CS0618: 'Flags.Navigation' is obsolete: 'Navigation is gone.'",
            "Program.cs(25,13): warning CS0618: 'DrawerAttribute.Expanded' is obsolete: 'Use ShowFoldout.'",
            "Program.cs(28,9): warning CS0612: 'OldType' is obsolete",
            "Program.cs(29,23): warning CS0618: 'UiInstance<Events>' is obsolete: 'Use UiObject instead'",
        ]
    );
}

#[test]
fn a_call_left_unawaited_in_an_async_method_is_warned_about() {
    // CS4014 over the whole call: in an `async` function for a call whose
    // result can be awaited, and outside one for a call of a method declared
    // `async` (as Roslyn has it), but not where the result is taken.
    let Some(bytes) = references() else {
        println!("note: the unawaited test was skipped; no .NET shared framework was found");
        return;
    };
    let program = r#"
using System.Threading.Tasks;
static class Program
{
    static async Task Work() { await Task.Yield(); }
    static Task<int> Value() => Task.FromResult(1);
    static async Task Run()
    {
        Work();
        _ = Work();
        await Work();
        Value();
        var kept = Work();
        System.Console.WriteLine();
    }
    static void Sync() { Work(); Value(); }
    static void Main() { }
}
"#;
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
    let compilation = Compilation::create_with_references(
        vec![parse(SourceText::new("Program.cs", program))],
        &images,
    );
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| compilation.render(entry))
        .filter(|line| line.contains("CS4014"))
        .collect();
    let message = "warning CS4014: Because this call is not awaited, execution of the current method continues before the call is completed. Consider applying the 'await' operator to the result of the call.";
    assert_eq!(
        diagnostics,
        [
            format!("Program.cs(9,9): {message}"),
            format!("Program.cs(12,9): {message}"),
            format!("Program.cs(16,26): {message}")
        ]
    );
}

/// `nuint.MaxValue > 1` was `-1 > 1`: an `nuint` compared, divided and
/// shifted right with the signed instructions. A shift count goes in masked
/// to the width of what is shifted (§12.11), which `shl` itself does not
/// promise; and a floating constant cast to an integer is the integer.
/// What is expected is what the program prints built by Roslyn.
#[test]
fn an_nuint_compares_divides_and_shifts_unsigned_and_a_shift_count_is_masked() {
    check(
        "NativeAndShifts",
        r#"
using System;
class NativeAndShifts {
    static nuint Big() => unchecked((nuint)(-1));
    static nuint One() => 1;
    static int Sh(int x, int n) => x << n;
    static long ShL(long x, int n) => x << n;
    static int Sr(int x, int n) => x >> n;
    static uint Sru(uint x, int n) => x >> n;
    static int Srr(int x, int n) => x >>> n;
    static void A() {
        nuint big = Big(), one = One();
        Console.WriteLine(big > one);      // True
        Console.WriteLine(big < one);      // False
        Console.WriteLine(big >= one);     // True
        Console.WriteLine(big <= one);     // False
    }
    static void B() {
        nuint big = Big();
        Console.WriteLine(big / 2 == (nuint)IntPtr.MaxValue);  // True
        Console.WriteLine(big % 10);       // 5 (64-bit)
        Console.WriteLine(big >> 60);      // 15
    }
    static void C() {
        nuint big = Big();
        big /= 2; Console.WriteLine(big == (nuint)IntPtr.MaxValue); // True
        big = Big(); big >>= 60; Console.WriteLine(big); // 15
        big = Big(); big %= 10; Console.WriteLine(big); // 5
    }
    static void D() {
        nint neg = -8;
        Console.WriteLine(neg >> 1);       // -4
        Console.WriteLine(neg / 2);        // -4
        Console.WriteLine(neg < 0);        // True
    }
    static void E() {
        Console.WriteLine(Sh(1, 33));      // 2
        Console.WriteLine(ShL(1, 65));     // 2
        Console.WriteLine(Sr(-16, 34));    // -4
        Console.WriteLine(Sru(0x80000000, 35)); // 268435456
        Console.WriteLine(Srr(-16, 33));   // 2147483640
        int x = 1; x <<= 33; Console.WriteLine(x); // 2
        long y = 1; y <<= 65; Console.WriteLine(y); // 2
    }
    static void F() {
        Console.WriteLine(1 << 33);        // 2 (constant)
        Console.WriteLine(1L << 65);       // 2
        Console.WriteLine(-16 >> 34);      // -4
        byte b = 1; int sh = 9; Console.WriteLine(b << sh); // 512
        short s = -1; Console.WriteLine(s >> 40);  // -1
    }
    static void G() {
        const int c = (int)3.7; Console.WriteLine(c); // 3
        Console.WriteLine((int)3.7);       // 3
        Console.WriteLine((int)-3.7);      // -3
        Console.WriteLine((long)1e10);     // 10000000000
        Console.WriteLine((byte)3.99f);    // 3
    }
    static void H() {
        const double d = (int)3.7 + 0.5; Console.WriteLine(d); // 3.5
        Console.WriteLine((int)3.7 / 2);   // 1
        Console.WriteLine((double)(int)2.9 * 2); // 4
        Console.WriteLine((char)65.7);     // A
        Console.WriteLine((uint)3.7m);     // 3
        Console.WriteLine((float)(int)7.9); // 7
    }
    static void Try(string name, Action a) {
        Console.Write(name + ": ");
        try { a(); } catch (Exception e) { Console.WriteLine(e.GetType().Name); }
    }
    static void Main() {
        Try("A", A); Try("B", B); Try("C", C); Try("D", D); Try("E", E); Try("F", F); Try("G", G); Try("H", H);
    }
}
"#,
        "A: True\nFalse\nTrue\nFalse\nB: True\n5\n15\nC: True\n15\n5\nD: -4\n-4\nTrue\nE: 2\n2\n-4\n268435456\n2147483640\n2\n2\nF: 2\n2\n-4\n512\n-1\nG: 3\n3\n-3\n10000000000\n3\nH: 3.5\n1\n4\nA\n3\n7\n",
    );
}

/// An enum over an unsigned type orders its members as unsigned numbers,
/// a lifted or compound shift masks its count like any other, and a cast of
/// a constant folds to the value the cast gives. Expected: Roslyn's build.
#[test]
fn unsigned_enums_lifted_shifts_and_constant_casts_agree_with_roslyn() {
    check(
        "UnsignedEnumsAndCasts",
        r#"
using System;
[Flags] enum U : uint { None = 0, Low = 1, Top = 0x80000000 }
enum UL : ulong { A = 1, Big = 0xFFFFFFFFFFFFFFF0 }
enum B : byte { X = 200, Y = 100 }
class UnsignedEnumsAndCasts {
    static nuint Big() => unchecked((nuint)(-1));
    static T Id<T>(T x) => x;
    static void Main() {
        nuint big = Big(); nuint two = Id<nuint>(2);
        Console.WriteLine((ulong)big);
        Console.WriteLine((double)big > 1e18);
        Console.WriteLine((long)(big / two));
        Console.WriteLine(big > two ? "gt" : "le");
        Console.WriteLine(Math.Max(big, two) == big);
        nuint? nb = big, nt = two;
        Console.WriteLine(nb > nt);
        Console.WriteLine(nb / nt == (nuint)IntPtr.MaxValue);
        Console.WriteLine(nb >> 60);
        if (big < two) Console.WriteLine("wrong"); else Console.WriteLine("right");
        while (big > 100) big /= 1000;
        Console.WriteLine(big);
        U top = Id(U.Top), low = Id(U.Low);
        Console.WriteLine(top > low);
        Console.WriteLine(top < low);
        Console.WriteLine(top >= low);
        Console.WriteLine(low <= top);
        Console.WriteLine(top.CompareTo(low) > 0);
        UL ub = Id(UL.Big), ua = Id(UL.A);
        Console.WriteLine(ub > ua);
        Console.WriteLine((ulong)ub);
        Console.WriteLine(ub - ua);
        B bx = Id(B.X), by = Id(B.Y);
        Console.WriteLine(bx > by);
        U? nt2 = top; U? nl = low;
        Console.WriteLine(nt2 > nl);
        int one = Id(1), n33 = Id(33), n65 = Id(65);
        long lone = Id(1L);
        int? none = one; int? ncount = n33;
        Console.WriteLine(none << ncount);
        Console.WriteLine(lone << n65);
        long? nlone = lone; Console.WriteLine(nlone << n65);
        uint ux = Id(0x80000000u); Console.WriteLine(ux >> n33);
        ulong ulx = Id(0x8000000000000000ul); Console.WriteLine(ulx >> n65);
        nint ni = Id<nint>(1); Console.WriteLine(ni << n65);
        nuint nu = Id<nuint>(1); Console.WriteLine(nu << n65);
        nu <<= n65; Console.WriteLine(nu);
        short sh = Id<short>(1); sh <<= n33; Console.WriteLine(sh);
        byte bb = Id<byte>(1); Console.WriteLine(bb << n33);
        sbyte sb = Id<sbyte>(-128); Console.WriteLine(sb >> n33);
        Console.WriteLine(sb >>> n33);
        char c = Id('A'); Console.WriteLine(c << n33);
        long big2 = Id(long.MinValue); big2 >>= n65; Console.WriteLine(big2);
        big2 >>>= n65; Console.WriteLine(big2);
        Console.WriteLine(one << -1);
        Console.WriteLine(lone << -1);
        Console.WriteLine(one << Id(-1));
        Console.WriteLine(lone << Id(-1));
        Console.WriteLine((int)Id(3.7));
        Console.WriteLine((int)3.7 + (int)-2.9);
        const long L = (long)1e15; Console.WriteLine(L);
        const byte By = (byte)255.9; Console.WriteLine(By);
        const char Ch = (char)66.2; Console.WriteLine(Ch);
        const float F = (float)0.1; Console.WriteLine(F == 0.1f);
        Console.WriteLine((float)0.1 == 0.1f);
        Console.WriteLine((double)0.1f == 0.1);
        Console.WriteLine((ulong)1.8e19);
        Console.WriteLine((uint)3e9);
        Console.WriteLine(unchecked((int)1e10) == unchecked((int)1e10));
        const int K = (int)2.5f * 2; Console.WriteLine(K);
        Console.WriteLine((B)1.9);
        Console.WriteLine((int)(B)200.5 + 1);
        switch (one) { case (int)1.9: Console.WriteLine("case 1"); break; default: Console.WriteLine("default"); break; }
        int[] arr = new int[(int)3.9]; Console.WriteLine(arr.Length);
    }
}
"#,
        "18446744073709551615\nTrue\n9223372036854775807\ngt\nTrue\nTrue\nTrue\n15\nright\n18\nTrue\nFalse\nTrue\nTrue\nTrue\nTrue\n18446744073709551600\n18446744073709551599\nTrue\nTrue\n2\n2\n2\n1073741824\n4611686018427387904\n2\n2\n2\n2\n2\n-64\n2147483584\n130\n-4611686018427387904\n6917529027641081856\n-2147483648\n-9223372036854775808\n-2147483648\n-9223372036854775808\n3\n1\n1000000000000000\n255\nB\nTrue\nTrue\nFalse\n18000000000000000000\n3000000000\nTrue\n4\n1\n201\ncase 1\n3\n",
    );
}

/// `(long)n` on an `nuint` is the language's conversion, not `UIntPtr`'s
/// operator to `uint`, which throws past four thousand million; and a
/// native integer reaches a `decimal` through the 64-bit integer of its
/// sign, where nothing at all was emitted. Expected: Roslyn's build.
#[test]
fn native_integers_convert_to_and_from_every_number() {
    check(
        "NativeConversions",
        r#"
using System;
class NativeConversions {
    static T Id<T>(T x) => x;
    static void Main() {
        nuint big = unchecked((nuint)(-1)); nint neg = Id<nint>(-5);
        Console.WriteLine((long)big); Console.WriteLine((ulong)big); Console.WriteLine((int)big); Console.WriteLine((uint)big);
        Console.WriteLine((short)big); Console.WriteLine((byte)big); Console.WriteLine((double)big); Console.WriteLine((float)big);
        Console.WriteLine((char)Id<nuint>(65)); Console.WriteLine((decimal)big); Console.WriteLine((nint)big);
        Console.WriteLine((long)neg); Console.WriteLine((ulong)neg); Console.WriteLine((int)neg); Console.WriteLine((uint)neg);
        Console.WriteLine((double)neg); Console.WriteLine((nuint)neg); Console.WriteLine((decimal)neg); Console.WriteLine((sbyte)neg);
        Console.WriteLine((nuint)Id(5)); Console.WriteLine((nuint)Id(5L)); Console.WriteLine((nuint)Id(5u)); Console.WriteLine((nuint)Id(5.9));
        Console.WriteLine((nint)Id(-5.9)); Console.WriteLine((nint)Id(-5L)); Console.WriteLine((nint)Id(3000000000u)); Console.WriteLine((nint)Id('A'));
        Console.WriteLine((nuint)Id<byte>(200)); Console.WriteLine((nint)Id<sbyte>(-3)); Console.WriteLine((nuint)Id(7m)); Console.WriteLine((nint)Id(DayOfWeek.Friday));
        Console.WriteLine((DayOfWeek)Id<nint>(2)); Console.WriteLine((DayOfWeek)Id<nuint>(3));
        try { Console.WriteLine(checked((int)big)); } catch (OverflowException) { Console.WriteLine("ovf1"); }
        try { Console.WriteLine(checked((nuint)neg)); } catch (OverflowException) { Console.WriteLine("ovf2"); }
        try { Console.WriteLine(checked((long)big)); } catch (OverflowException) { Console.WriteLine("ovf3"); }
        try { Console.WriteLine(checked(big + 1)); } catch (OverflowException) { Console.WriteLine("ovf4"); }
        long l = neg; double d = big; ulong ul = big; nint fromInt = Id(7); nuint fromUint = Id(7u);
        Console.WriteLine(l + " " + d + " " + ul + " " + fromInt + " " + fromUint);
        IntPtr ip = new IntPtr(42); UIntPtr up = new UIntPtr(43);
        Console.WriteLine((int)ip + (int)up + (long)ip + (long)(ulong)up);
        Console.WriteLine(ip == (IntPtr)42); Console.WriteLine(up != UIntPtr.Zero); Console.WriteLine(ip + 1); Console.WriteLine(up > 1);
    }
}
"#,
        "-1\n18446744073709551615\n-1\n4294967295\n-1\n255\n1.8446744073709552E+19\n1.8446744E+19\nA\n18446744073709551615\n-1\n-5\n18446744073709551611\n-5\n4294967291\n-5\n18446744073709551611\n-5\n-5\n5\n5\n5\n5\n-5\n-5\n3000000000\n65\n200\n-3\n7\n5\nTuesday\nWednesday\novf1\novf2\novf3\novf4\n-5 1.8446744073709552E+19 18446744073709551615 7 7\n170\nTrue\nTrue\n43\nTrue\n",
    );
}

/// Inside `checked`, `nuint.MaxValue + 1` overflows — by the language's
/// `+`, not `UIntPtr.op_Addition`, which wraps — and an `nuint` past
/// `long.MaxValue` is no `long`. Expected: Roslyn's build.
#[test]
fn checked_native_arithmetic_and_conversions_trap_by_sign() {
    check(
        "CheckedNative",
        r#"
using System;
class CheckedNative {
    static T Id<T>(T x) => x;
    static void Main() {
        nuint big = unchecked((nuint)(-1)); nuint one = Id<nuint>(1); nint max = IntPtr.MaxValue; nint mone = Id<nint>(-1);
        try { Console.WriteLine(checked(big + 1)); } catch (OverflowException) { Console.WriteLine("ovf4"); }
        try { Console.WriteLine(checked(big + one)); } catch (OverflowException) { Console.WriteLine("ovf5"); }
        try { Console.WriteLine(checked(one - big)); } catch (OverflowException) { Console.WriteLine("ovf6"); }
        try { Console.WriteLine(checked(big * big)); } catch (OverflowException) { Console.WriteLine("ovf7"); }
        try { Console.WriteLine(checked(max + 1)); } catch (OverflowException) { Console.WriteLine("ovf8"); }
        try { Console.WriteLine(checked(mone + mone)); } catch (OverflowException) { Console.WriteLine("ovf9"); }
        try { checked { big++; } Console.WriteLine(big); } catch (OverflowException) { Console.WriteLine("ovf10"); }
        try { checked { big += one; } Console.WriteLine(big); } catch (OverflowException) { Console.WriteLine("ovf11"); }
        try { Console.WriteLine(checked((int)big)); } catch (OverflowException) { Console.WriteLine("ovf1"); }
        try { Console.WriteLine(checked((long)big)); } catch (OverflowException) { Console.WriteLine("ovf3"); }
        try { Console.WriteLine(checked((uint)big)); } catch (OverflowException) { Console.WriteLine("ovf12"); }
        try { Console.WriteLine(checked((ulong)mone)); } catch (OverflowException) { Console.WriteLine("ovf13"); }
        try { Console.WriteLine(checked((byte)mone)); } catch (OverflowException) { Console.WriteLine("ovf14"); }
        try { Console.WriteLine(checked((sbyte)one)); } catch (OverflowException) { Console.WriteLine("ovf15"); }
        try { Console.WriteLine(checked((ulong)big)); } catch (OverflowException) { Console.WriteLine("ovf16"); }
        try { Console.WriteLine(checked((long)mone)); } catch (OverflowException) { Console.WriteLine("ovf17"); }
        try { Console.WriteLine(checked((char)big)); } catch (OverflowException) { Console.WriteLine("ovf18"); }
        try { Console.WriteLine(checked((double)big)); } catch (OverflowException) { Console.WriteLine("ovf19"); }
        try { Console.WriteLine(checked((decimal)big)); } catch (OverflowException) { Console.WriteLine("ovf20"); }
        try { Console.WriteLine(checked((nuint)Id(-1m))); } catch (OverflowException) { Console.WriteLine("ovf21"); }
        try { Console.WriteLine(checked((nint)Id(7e28m))); } catch (OverflowException) { Console.WriteLine("ovf22"); }
    }
}
"#,
        "ovf4\novf5\novf6\novf7\novf8\n-2\novf10\novf11\novf1\novf3\novf12\novf13\novf14\n1\n18446744073709551615\n-1\novf18\n1.8446744073709552E+19\n18446744073709551615\novf21\novf22\n",
    );
}

/// The errors `source` gets bound against the framework and `library`, as
/// `CS0000 'underlined'`, in the order of where they are; `None` where there
/// is no framework to bind against.
fn errors_with_library(name: &str, library: &str, source: &str) -> Option<Vec<String>> {
    let mut bytes = references()?;
    let library_name = format!("{name}Library");
    let compilation = compiled(&library_name, library, &bytes);
    let emitted = rustlyn_emit::emit_library(&compilation, &library_name)
        .unwrap_or_else(|error| panic!("{library_name} could not be emitted: {error}"));
    bytes.push(emitted.assembly);
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
    let compilation = Compilation::create_with_references(
        vec![parse(SourceText::new("Program.cs", source))],
        &images,
    );
    let mut found: Vec<_> = compilation
        .semantic_diagnostics()
        .into_iter()
        .map(|entry| entry.diagnostic)
        .filter(rustlyn_diagnostics::Diagnostic::is_error)
        .collect();
    found.sort_by_key(|diagnostic| (diagnostic.span().start(), diagnostic.code()));
    Some(
        found
            .iter()
            .map(|diagnostic| {
                let span = diagnostic.span();
                format!(
                    "{} '{}'",
                    diagnostic.code(),
                    &source[span.start() as usize..span.end() as usize]
                )
            })
            .collect(),
    )
}

/// What a library keeps for the types derived from its own.
const PROTECTED_LIBRARY: &str = r#"
using System;
public class Base
{
    protected int Prot;
    protected internal int ProtInt;
    protected static int SProt;
    protected Base() { }
    protected virtual void OnThing() { }
    protected internal virtual void OnOther() { }
    protected int Prop { get; set; }
    public int Mixed { get; protected set; }
    protected static void Helper() { }
    public static void Pub() { }
}
public class Mid : Base { protected override void OnThing() { } }
"#;

/// A protected member read out of a reference was accessible from any
/// class: `stream.Dispose(true)` compiled in one that is no `Stream`, and
/// the runtime refused it. It is for the types derived from its own, as one
/// in the same compilation is; `protected internal` from another assembly
/// is protected and no more. The errors are the ones Roslyn reports:
/// `Dispose(true)` is a public `Dispose()` given one too many (CS1501), as
/// a name is looked up among what may be called before arguments count.
#[test]
fn a_protected_member_of_a_reference_is_for_derived_types_only() {
    let stranger = r#"
using System.IO;
using System.Collections.ObjectModel;
class Stranger
{
    void M(Base b, Mid m, Stream s, TextWriter w, Collection<int> c)
    {
        b.Prot = 1;
        b.ProtInt = 2;
        m.OnThing();
        b.OnOther();
        b.Prop = 1;
        Base.Helper();
        var x = Base.SProt;
        s.Dispose(true);
        var n = w.CoreNewLine;
        c.ClearItems();
        var items = c.Items;
        Base.Pub();
        var y = b.Mixed;
        object o = MemberwiseClone();
    }
}
"#;
    let Some(found) = errors_with_library("ProtectedAbroad", PROTECTED_LIBRARY, stranger) else {
        println!("note: skipped; no .NET shared framework was found");
        return;
    };
    assert_eq!(
        found,
        [
            "CS0122 'Prot'",
            "CS0122 'ProtInt'",
            "CS0122 'OnThing'",
            "CS0122 'OnOther'",
            "CS0122 'Prop'",
            "CS0122 'Helper'",
            "CS0122 'SProt'",
            "CS1501 'Dispose'",
            "CS0122 'CoreNewLine'",
            "CS0122 'ClearItems'",
            "CS0122 'Items'",
        ]
    );
}

#[test]
fn a_type_derived_from_a_references_reaches_its_protected_members() {
    let derived = r#"
using System;
using System.IO;
using System.Collections.ObjectModel;
class Derived : Mid
{
    Derived() : base() { }
    void M(Derived d)
    {
        Prot = 1; ProtInt = 2; SProt = 3; OnThing(); OnOther(); Prop = 4; Mixed = 5; Helper();
        d.Prot = 1;
        base.OnThing();
        Action a = () => { Prot++; OnThing(); };
        a();
    }
    protected override void OnThing() { base.OnThing(); }
    static void S(Derived d) { d.OnThing(); }
    class Nested { void Q(Derived d) { d.Prot = 1; d.OnThing(); Helper(); } }
}
class MyStream : MemoryStream
{
    protected override void Dispose(bool disposing) { base.Dispose(disposing); }
    void N(MyStream other) { other.Dispose(true); Dispose(false); }
}
class MyCollection : Collection<string>
{
    protected override void InsertItem(int index, string item) { base.InsertItem(index, item); Items.Add(item); }
    void Clear2() { ClearItems(); var i = Items; }
}
class MyWriter : StringWriter { string NL => new string(CoreNewLine); }
struct Value { object Clone() => MemberwiseClone(); }
class Elsewhere { int M(Derived d) => d.Mixed; }
"#;
    let Some(found) = errors_with_library("ProtectedDerived", PROTECTED_LIBRARY, derived) else {
        println!("note: skipped; no .NET shared framework was found");
        return;
    };
    assert_eq!(found, Vec::<String>::new());
}

/// The nested types a library keeps for the types derived from its own.
const NESTED_LIBRARY: &str = r#"
public class Base
{
    protected class Prot { public int V; public class Deep { } }
    protected internal class ProtInt { }
    internal class Hidden { }
    public class Pub { }
    protected enum Kind { A }
    public class Open { protected class InnerProt { } public class InnerPub { } }
}
public class Gen<T> { protected class In { public T V; } }
public class Mid : Base { }
"#;

/// A protected type read out of a reference could be named from any class:
/// `new Base.Prot()` compiled in one that is no `Base`. It is for the types
/// derived from its owner, as one in the same compilation is, and
/// `protected internal` from another assembly is protected and no more.
/// The errors are at the type's own name, as Roslyn has them.
#[test]
fn a_protected_nested_type_of_a_reference_is_for_derived_types_only() {
    let stranger = r#"
using System;
using System.Collections.Generic;
class Stranger : List<Base.Prot>
{
    Base.Prot field;
    Base.ProtInt other;
    void M(object o, Mid m)
    {
        var a = new Base.Prot();
        Base.Prot b = null;
        var c = (Base.Prot)o;
        var t = typeof(Base.Prot);
        var l = new List<Base.Prot>();
        bool z = o is Base.Prot;
        var d = new Base.Prot.Deep();
        var k = Base.Kind.A;
        var g = new Gen<int>.In();
        var viaMid = new Mid.Prot();
        var i = new Base.Open.InnerProt();
        var fine = new Base.Pub();
        var alsoFine = new Base.Open.InnerPub();
    }
}
"#;
    let Some(found) = errors_with_library("NestedAbroad", NESTED_LIBRARY, stranger) else {
        println!("note: skipped; no .NET shared framework was found");
        return;
    };
    assert_eq!(
        found,
        [
            "CS0122 'Prot'",
            "CS0122 'Prot'",
            "CS0122 'ProtInt'",
            "CS0122 'Prot'",
            "CS0122 'Prot'",
            "CS0122 'Prot'",
            "CS0122 'Prot'",
            "CS0122 'Prot'",
            "CS0122 'Prot'",
            "CS0122 'Prot'",
            "CS0122 'Kind'",
            "CS0122 'In'",
            "CS0122 'Prot'",
            "CS0122 'InnerProt'",
        ]
    );
}

#[test]
fn a_type_derived_from_a_references_reaches_its_protected_nested_types() {
    let derived = r#"
using System;
using System.Collections.Generic;
class Derived : Base
{
    Base.Prot f1; Derived.Prot f2; Prot f3; Base.Prot.Deep f4; Base.ProtInt f5; Base.Kind f6;
    List<Base.Prot> list;
    Base.Prot M(Base.Prot p) => p;
    class Inner : Base.Prot { Base.Prot x; void Z() { var a = new Base.Prot(); } }
    void N(object o)
    {
        var a = new Base.Prot(); var b = new Derived.Prot(); var c = new Prot();
        var d = new Base.Prot.Deep(); var e = Base.Kind.A; var g = typeof(Base.Prot);
        var h = (Base.Prot)o; bool z = o is Base.Prot; var i = new List<Base.Prot>();
        var j = new Base.ProtInt(); var k = new Base.Pub(); var l = new Base.Open.InnerPub();
        Action act = () => { var w = new Base.Prot(); };
        void Local() { var w = new Base.Prot(); }
    }
}
class FurtherDown : Derived { void N() { var a = new Base.Prot(); var b = new FurtherDown.Prot(); } }
class ThroughMid : Mid { void N() { var a = new Base.Prot(); var b = new Mid.Prot(); } }
class Generic<T> : Base { void N() { var a = new Base.Prot(); var b = new Generic<T>.Prot(); var c = new Generic<int>.Prot(); } }
class OfGeneric : Gen<string> { void N() { var a = new Gen<string>.In(); var b = new In(); var c = new OfGeneric.In(); } }
class OfGenericAgain<U> : Gen<U>
{
    void N() { var a = new Gen<U>.In(); var b = new OfGenericAgain<U>.In(); }
    class Q { void R() { var a = new Gen<U>.In(); } }
}
class Outside { class Nested : Base { void N() { var a = new Base.Prot(); } } }
class Deep : Base { class A { class B { void N() { var a = new Base.Prot(); var b = new Deep.Prot(); } } } }
class FromOpen : Base.Open { void N() { var a = new InnerProt(); var b = new Base.Open.InnerProt(); } }
class Anyone { void N() { var a = new Base.Pub(); var b = new Base.Open.InnerPub(); } }
"#;
    let Some(found) = errors_with_library("NestedDerived", NESTED_LIBRARY, derived) else {
        println!("note: skipped; no .NET shared framework was found");
        return;
    };
    assert_eq!(found, Vec::<String>::new());
}

/// A `private protected` type is for the derived types of its own assembly:
/// read out of a reference it is for none, a type derived from its owner
/// included, while `protected internal` and `protected` beside it are.
/// Roslyn calls it inaccessible (CS0122); the reference loader does not read
/// what no other assembly can use, so here the name is not there (CS0426).
#[test]
fn a_private_protected_nested_type_of_a_reference_is_for_none() {
    let library = r#"
public class Base { private protected class PrivProt { } protected internal class ProtInt { } protected class Prot { } }
"#;
    let user = r#"
class Derived : Base
{
    void N() { var a = new Base.PrivProt(); var b = new Base.ProtInt(); var c = new Base.Prot(); }
}
class Stranger { void N() { var a = new Base.PrivProt(); } }
"#;
    let Some(found) = errors_with_library("PrivateProtectedAbroad", library, user) else {
        println!("note: skipped; no .NET shared framework was found");
        return;
    };
    assert_eq!(found, ["CS0426 'PrivProt'", "CS0426 'PrivProt'"]);
}

/// The assembly an `[InternalsVisibleTo]` names reaches the library's
/// `protected internal` types as internal ones, from any class.
#[test]
fn a_friend_reaches_a_protected_internal_nested_type_of_a_reference() {
    let Some(mut bytes) = references() else {
        println!("note: skipped; no .NET shared framework was found");
        return;
    };
    let library = r#"
[assembly: System.Runtime.CompilerServices.InternalsVisibleTo("Friend")]
public class Base { protected internal class ProtInt { } protected class Prot { } }
"#;
    let compilation = compiled("FriendNestedLibrary", library, &bytes);
    let emitted = rustlyn_emit::emit_library(&compilation, "FriendNestedLibrary")
        .unwrap_or_else(|error| panic!("FriendNestedLibrary could not be emitted: {error}"));
    bytes.push(emitted.assembly);
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
    let program =
        "class Anyone { void M() { var a = new Base.ProtInt(); var b = new Base.Prot(); } }";
    let found = |name: &str| -> Vec<String> {
        let trees = vec![parse(SourceText::new("Program.cs", program))];
        let compilation = Compilation::create_with_references_as(trees, &images, name);
        compilation
            .semantic_diagnostics()
            .iter()
            .map(|entry| compilation.render(entry))
            .collect()
    };
    let friend = found("Friend");
    assert_eq!(friend.len(), 1, "{friend:#?}");
    assert!(
        friend[0].contains("CS0122") && friend[0].contains("'Base.Prot'"),
        "{friend:#?}"
    );
    let stranger = found("Stranger");
    assert_eq!(stranger.len(), 2, "{stranger:#?}");
}

#[test]
fn a_const_decimal_from_a_non_decimal_constant_loads_as_a_decimal() {
    check(
        "decimal_from_integer_constants",
        r#"
using System;
using System.Reflection;
class P
{
    const decimal F1 = (byte)3;
    const decimal F2 = 'b';
    const decimal F3 = 5L;
    const decimal F4 = ulong.MaxValue;
    const decimal F5 = (short)-3;
    const decimal F6 = 'a' + 1;
    const decimal F7 = 1.5m + 2;
    const decimal F8 = long.MinValue;
    const decimal F9 = uint.MaxValue;
    const decimal F12 = -F4;
    const decimal F13 = F4 * 2;
    public const decimal PubB = (ulong)long.MaxValue + 1;
    static void M(decimal d = 5, decimal e = 'c', decimal? n = 3L, decimal? z = null, decimal q = ulong.MaxValue)
        => Console.WriteLine($"{d} {e} {n} {z} {q}");
    static void Main()
    {
        const decimal c1 = (byte)3; const decimal c2 = 'b'; const decimal c3 = 5L; const decimal c4 = ulong.MaxValue;
        const decimal c5 = (short)-3; const decimal c6 = 'a' + 1; const decimal c7 = 1.5m + 2; const decimal c8 = long.MinValue;
        Console.WriteLine($"{c1} {c2} {c3} {c4} {c5} {c6} {c7} {c8}");
        Console.WriteLine($"{F1} {F2} {F3} {F4} {F5} {F6} {F7} {F8} {F9} {F12} {F13}");
        Console.WriteLine(c4 + c3 * 2 + F1);
        decimal? o = 5L;
        Console.WriteLine(o);
        M(); M(1, 'd'); M(q: 2);
        foreach (var name in new[] { "F4", "F6", "F8", "F9", "F12", "F13", "PubB" })
        {
            var data = typeof(P).GetField(name, BindingFlags.NonPublic | BindingFlags.Public | BindingFlags.Static).GetCustomAttributesData();
            Console.Write(name);
            foreach (var d in data)
                foreach (var a in d.ConstructorArguments) Console.Write(" " + a.Value);
            Console.WriteLine();
        }
        foreach (var p in typeof(P).GetMethod("M", BindingFlags.NonPublic | BindingFlags.Static).GetParameters())
        {
            Console.Write(p.Name + " " + p.RawDefaultValue);
            foreach (var d in p.GetCustomAttributesData())
                if (d.AttributeType.Name == "DecimalConstantAttribute")
                    foreach (var a in d.ConstructorArguments) Console.Write(" " + a.Value);
            Console.WriteLine();
        }
    }
}
"#,
        "3 98 5 18446744073709551615 -3 98 3.5 -9223372036854775808\n3 98 5 18446744073709551615 -3 98 3.5 -9223372036854775808 4294967295 -18446744073709551615 36893488147419103230\n18446744073709551628\n5\n5 99 3  18446744073709551615\n1 100 3  18446744073709551615\n5 99 3  2\nF4 0 0 0 4294967295 4294967295\nF6 0 0 0 0 98\nF8 0 128 0 2147483648 0\nF9 0 0 0 0 4294967295\nF12 0 128 0 4294967295 4294967295\nF13 0 0 1 4294967295 4294967294\nPubB 0 0 0 2147483648 0\nd 5 0 0 0 0 5\ne 99 0 0 0 0 99\nn 3 0 0 0 0 3\nz \nq 18446744073709551615 0 0 0 4294967295 4294967295\n",
    );
}

/// An `if` with an `else`, and every loop, inside a `catch` or a `finally`.
/// Nothing branches to a handler, so while its body was being written
/// everything in it looked unreachable: the `if` left out the jump over its
/// `else` and ran both branches, and a loop left out its jump back and ran
/// once. In iterators and `async` methods too.
#[test]
fn branches_and_loops_inside_a_catch_or_a_finally_run_as_written() {
    check(
        "HandlerControlFlow",
        r#"
using System;
using System.Collections.Generic;
using System.Threading.Tasks;
class P
{
    static void A(bool c) { try { throw new Exception(); } catch (Exception) { if (c) Console.Write("a "); else Console.Write("b "); } }
    static void B(bool c) { try { } finally { if (c) Console.Write("a "); else Console.Write("b "); } }
    static void C() { try { throw new Exception(); } catch { int i = 0; while (i < 3) { Console.Write("c" + i + " "); i++; } } finally { for (int j = 0; j < 2; j++) Console.Write("f" + j + " "); foreach (var x in new[] { 7, 8 }) Console.Write(x + " "); int k = 0; do { k++; } while (k < 5); Console.Write(k + " "); } }
    static IEnumerable<int> It() { int fuel = 0; try { yield return 1; } finally { while (true) { if (++fuel > 3) break; Console.Write("loop" + fuel + " "); } } }
    static async Task As(bool c) { try { await Task.Yield(); throw new Exception(); } catch (Exception) when (c || !c) { if (c) Console.Write("x "); else Console.Write("y "); for (int i = 0; i < 2; i++) Console.Write(i + " "); } finally { if (!c) Console.Write("z "); else Console.Write("w "); } }
    static int D(int n) { try { return n; } finally { if (n > 0) { try { throw new Exception(); } catch { if (n > 1) Console.Write("deep "); else Console.Write("shallow "); } } else Console.Write("zero "); } }
    static void Main()
    {
        A(true); A(false); B(true); B(false); Console.WriteLine(); C(); Console.WriteLine();
        foreach (var v in It()) Console.Write(v + " "); Console.WriteLine();
        As(true).Wait(); As(false).Wait(); Console.WriteLine(); D(2); D(1); D(0); Console.WriteLine();
        using (var ms = new System.IO.MemoryStream()) { if (ms.Length == 0) Console.Write("u1 "); else Console.Write("u2 "); }
        lock (typeof(P)) { for (int i = 0; i < 2; i++) Console.Write("l" + i + " "); }
        Console.WriteLine();
    }
}
"#,
        "a b a b \nc0 c1 c2 f0 f1 7 8 5 \n1 loop1 loop2 loop3 \nx 0 1 w y 0 1 z \ndeep shallow zero \nu1 l0 l1 \n",
    );
}

/// A relational pattern on a native integer compares native integers, the
/// constant as one, and a pointer takes a native integer for an offset.
/// `n switch { > 5 => ... }` asked whether the `nint` was an `int` and so
/// never matched, and `p + n` was refused.
#[test]
fn a_native_integer_is_matched_by_a_relational_pattern_and_offsets_a_pointer() {
    check(
        "native_integer_patterns_and_pointers",
        r#"
using System;
unsafe class P
{
    static string K(nint n) => n switch { 5 => "five", > 5 => "more", _ => "less" };
    static string U(nuint n) => n switch { 5 => "five", > 5 and < 100 => "mid", >= 100 => "big", _ => "less" };
    static string N(nint? n) => n switch { null => "null", 5 => "five", > 5 => "more", _ => "less" };
    static string O(object o) => o switch { nint and > 5 => "nint>5", nuint and <= 3 => "nuint<=3", int and > 5 => "int>5", _ => "other" };
    static void Main()
    {
        nint a = 9; nuint b = 50; nuint big = nuint.MaxValue; nint? nn = 7; nuint? nu = 2;
        Console.WriteLine($"{K(9)} {K(5)} {K(-1)} {U(50)} {U(200)} {U(1)} {a is > 5} {a is < 5 or 9} {b is >= 50 and <= 50} {a is not (> 10)}");
        Console.WriteLine($"{N(9)} {N(5)} {N(null)} {N(-3)} {O((nint)9)} {O((nuint)2)} {O(9)} {O(9L)} {big is > 5} {big is < 5} {nn is > 5} {nu is >= 2 and <= 2}");
        nint n = 2; nuint u = 3; nint neg = -1;
        int* p = stackalloc int[8]; for (int i = 0; i < 8; i++) p[i] = i * 10;
        long* q = stackalloc long[8]; for (int i = 0; i < 8; i++) q[i] = i * 100;
        int* e = p + 5; e -= n; e += u;
        Console.WriteLine($"{*(p + n)} {*(n + p)} {*(p + u)} {*(q + n)} {*(p + 4 - u)} {*(p + 3 + neg)} {*e} {e - p} {p[n]} {p[u]} {(p + u) > p}");
    }
}
"#,
        "more five less mid big less True True True True\nmore five null less nint>5 nuint<=3 int>5 other True False True True\n20 20 30 200 10 20 60 6 20 30 True\n",
    );
}

#[test]
fn a_const_decimal_worked_out_from_constants_has_its_decimal_constant() {
    // Every one of these is a constant to Roslyn, which writes the
    // `[DecimalConstant]` another assembly reads it back by: the scale (what
    // `1.5m * 2.0m` keeps is `3.00`), the sign (of a zero as well), and the
    // 96 bits rounded as the framework rounds them. Output as Roslyn's own
    // build of the program printed it.
    check(
        "decimal_constants_worked_out",
        r#"
using System;
using System.Linq;
using System.Reflection;
enum E : byte { A = 3, B = 200 }
class P
{
    public const decimal L = (decimal)3.5;
    public const decimal N = 100m / 3;
    public const decimal T = 10 / 4m;
    public const decimal V = (decimal)1.5f;
    public const decimal W = -(decimal)0.25;
    public const decimal Third = 1m / 3;
    public const decimal TwoThirds = 2m / 3;
    public const decimal Trailing = 1.50m;
    public const decimal Product = 1.5m * 2.0m;
    public const decimal NegZero = -0m;
    public const decimal NegZeroProduct = 1m * -0m;
    public const decimal Max = decimal.MaxValue;
    public const decimal Min = decimal.MinValue;
    public const decimal NearMax = decimal.MaxValue - 0.4m;
    public const decimal Tiny = 0.0000000000000000000000000001m * 0.1m;
    public const decimal Sum = 0.1m + 0.20m;
    public const decimal Rem = 5.5m % 2m;
    public const decimal RemNeg = -7m % 3m;
    public const decimal FromFloat = (decimal)0.1f;
    public const decimal FromDouble = (decimal)0.1;
    public const decimal FromBig = (decimal)1.2345678901234567e20;
    public const decimal FromSmall = (decimal)1e-5;
    public const decimal FromLost = (decimal)1e-30;
    public const decimal FromEnum = (decimal)E.B + 1;
    public const decimal FromChar = 'a' + 0.5m;
    public const decimal Nested = ((1.5m + 2) * (3 - 1m)) / 4;
    public const decimal Unary = +(-L);
    public const int ToInt = (int)3.7m;
    public const long ToLong = (long)-3.7m;
    public const byte ToByte = (byte)255.9m;
    public const char ToChar = (char)65.5m;
    public const double ToDouble = (double)(1m / 3);
    public const float ToFloat = (float)0.1m;
    public const bool Less = 1m < 2m;
    public const bool Same = 1.0m == 1.00m;
    public const bool Other = L != T;
    public const int FromField = (int)(L * 2);
    static void D(decimal a = (decimal)3.5, decimal b = 100m / 3, decimal c = 10 / 4m, decimal? d = (decimal)1.5f, decimal e = -(decimal)0.25,
        decimal f = 1m % 3, decimal g = (decimal)E.A, decimal h = L * 2, int i = (int)3.5m, double j = (double)1.5m, bool k = 1m < 2m)
    {
        Console.WriteLine($"{a} {b} {c} {d} {e} {f} {g} {h} {i} {j} {k}");
    }
    static string Show(decimal d)
    {
        var bits = decimal.GetBits(d);
        return $"{bits[3] >> 16 & 255}/{(bits[3] < 0 ? 1 : 0)}/{(uint)bits[2]}/{(uint)bits[1]}/{(uint)bits[0]}";
    }
    static void Main()
    {
        D();
        foreach (var f in typeof(P).GetFields(BindingFlags.Public | BindingFlags.Static).OrderBy(f => f.Name, StringComparer.Ordinal))
        {
            var value = f.GetValue(null);
            var attribute = f.GetCustomAttributesData().FirstOrDefault(a => a.AttributeType.Name == "DecimalConstantAttribute");
            string shown = value is decimal d ? Show(d) : value is double x ? BitConverter.DoubleToInt64Bits(x).ToString() : value is float y ? BitConverter.SingleToInt32Bits(y).ToString() : value.ToString();
            Console.WriteLine(f.Name + " " + shown + (attribute == null ? "" : " [" + string.Join(",", attribute.ConstructorArguments.Select(a => a.Value)) + "]"));
        }
        foreach (var p in typeof(P).GetMethod("D", BindingFlags.NonPublic | BindingFlags.Static).GetParameters())
        {
            var attribute = p.GetCustomAttributesData().FirstOrDefault(a => a.AttributeType.Name == "DecimalConstantAttribute");
            Console.WriteLine(p.Name + " " + (p.RawDefaultValue ?? "null") + (attribute == null ? "" : " [" + string.Join(",", attribute.ConstructorArguments.Select(a => a.Value)) + "]"));
        }
        const decimal local = 100m / 3 + (decimal)0.5;
        Console.WriteLine(local);
        switch (3)
        {
            case (int)(1.5m + 1.5m): Console.WriteLine("three"); break;
        }
    }
}
"#,
        "3.5 33.333333333333333333333333333 2.5 1.5 -0.25 1 3 7.0 3 1.5 True\nFromBig 0/0/6/2974719873/792416896 [0,0,6,2974719873,792416896]\nFromChar 1/0/0/0/975 [1,0,0,0,975]\nFromDouble 1/0/0/0/1 [1,0,0,0,1]\nFromEnum 0/0/0/0/201 [0,0,0,0,201]\nFromField 7\nFromFloat 1/0/0/0/1 [1,0,0,0,1]\nFromLost 0/0/0/0/0 [0,0,0,0,0]\nFromSmall 5/0/0/0/1 [5,0,0,0,1]\nL 1/0/0/0/35 [1,0,0,0,35]\nLess True\nMax 0/0/4294967295/4294967295/4294967295 [0,0,4294967295,4294967295,4294967295]\nMin 0/1/4294967295/4294967295/4294967295 [0,128,4294967295,4294967295,4294967295]\nN 27/0/1807003620/3475376110/894784853 [27,0,1807003620,3475376110,894784853]\nNearMax 0/0/4294967295/4294967295/4294967295 [0,0,4294967295,4294967295,4294967295]\nNegZero 0/0/0/0/0 [0,128,0,0,0]\nNegZeroProduct 0/0/0/0/0 [0,128,0,0,0]\nNested 2/0/0/0/175 [2,0,0,0,175]\nOther True\nProduct 2/0/0/0/300 [2,0,0,0,300]\nRem 1/0/0/0/15 [1,0,0,0,15]\nRemNeg 0/1/0/0/1 [0,128,0,0,1]\nSame True\nSum 2/0/0/0/30 [2,0,0,0,30]\nT 1/0/0/0/25 [1,0,0,0,25]\nThird 28/0/180700362/347537611/89478485 [28,0,180700362,347537611,89478485]\nTiny 28/0/0/0/0 [28,0,0,0,0]\nToByte 255\nToChar A\nToDouble 4599676419421066582\nToFloat 1036831949\nToInt 3\nToLong -3\nTrailing 2/0/0/0/150 [2,0,0,0,150]\nTwoThirds 28/0/361400724/695075222/178956971 [28,0,361400724,695075222,178956971]\nUnary 1/1/0/0/35 [1,128,0,0,35]\nV 1/0/0/0/15 [1,0,0,0,15]\nW 2/1/0/0/25 [2,128,0,0,25]\na 3.5 [1,0,0,0,35]\nb 33.333333333333333333333333333 [27,0,1807003620,3475376110,894784853]\nc 2.5 [1,0,0,0,25]\nd 1.5 [1,0,0,0,15]\ne -0.25 [2,128,0,0,25]\nf 1 [0,0,0,0,1]\ng 3 [0,0,0,0,3]\nh 7.0 [1,0,0,0,70]\ni 3\nj 1.5\nk True\n33.833333333333333333333333333\nthree\n",
    );
}

#[test]
fn nint_and_nuint_reach_static_members_unless_a_name_answers_first() {
    check(
        "native_integer_static_members",
        r#"
using System;
class P
{
    static unsafe void Main()
    {
        nint x = nint.MaxValue;
        nint y = nint.MinValue;
        nuint z = nuint.MaxValue;
        nuint w = nuint.MinValue;
        Console.WriteLine($"{x} {y} {z} {w} {nint.Size} {nuint.Size} {nint.Zero == 0} {nint.Parse("1")} {nuint.Parse("2")}");
        Console.WriteLine(typeof(nint));
        Console.WriteLine(default(nint));
        Console.WriteLine(sizeof(nint) + sizeof(nuint));
        Console.WriteLine(nameof(nint.MaxValue));
        Console.WriteLine(nint.MaxValue.ToString());
        Console.WriteLine((nint)1 + nint.Size);
        Console.WriteLine(nint.TryParse("77", out var q) + " " + q);
        Other.Run();
    }
}
class Other
{
    class nuint { public static int Zero = 9; }
    public static void Run()
    {
        Console.WriteLine(nuint.Zero);
        var nint = new { MaxValue = 5 };
        Console.WriteLine(nint.MaxValue);
    }
}
"#,
        "9223372036854775807 -9223372036854775808 18446744073709551615 0 8 8 True 1 2\nSystem.IntPtr\n0\n16\nMaxValue\n9223372036854775807\n9\nTrue 77\n9\n5\n",
    );
}

#[test]
fn a_native_integer_meets_the_other_numbers_in_operators() {
    check(
        "native_integer_with_longs_and_floats",
        r#"
using System;
class P {
    static void Main() {
        ulong u = 5; long l = -3; float f = 1e30f; double d = 2;
        Console.WriteLine($"{l < nint.MinValue} {l > nint.MaxValue} {u > nuint.MaxValue} {f >= nint.MaxValue} {f <= nint.MinValue} {f >= nuint.MaxValue} {d < nint.MaxValue}");
        nint a = (f >= nint.MaxValue) ? nint.MaxValue : (nint)1;
        Console.WriteLine($"{a} {nint.MaxValue - 1} {nuint.MaxValue / 2} {nint.MaxValue == IntPtr.MaxValue} {IntPtr.MaxValue > l} {l + nint.Size} {IntPtr.Size * 2}");
    }
}
"#,
        "False False False True False True True\n9223372036854775807 9223372036854775806 9223372036854775807 True True 5 16\n",
    );
}

#[test]
fn native_integer_arithmetic_comparison_and_compound_assignment_match_roslyn() {
    check(
        "native_integer_operator_table",
        r#"
using System;
class P {
  static nint Ret() => nint.MaxValue;
  static void Main() {
    nint n = -3; nuint u = 7; long l = long.MinValue; ulong ul = ulong.MaxValue; int i = -2; uint ui = uint.MaxValue; float f = 1e30f; double d = 2.5; decimal m = 2.5m;
    nint nmax = nint.MaxValue, nmin = nint.MinValue; nuint umax = nuint.MaxValue; short sh = -1; char c = 'A'; byte b = 200; ushort us = 65535; sbyte sb = -128;
    Console.WriteLine($"{n + l} {n * l} {n - ui} {n + ui} {n * ui} {u + ul} {u - ul} {u * ul} {u + ui} {u + b} {u + us} {u + c}");
    Console.WriteLine($"{n + f} {n * d} {n / m} {u + f} {u * d} {u / m} {nmax + f} {nmax + d} {nmax + m} {umax + f} {umax + d} {umax + m}");
    Console.WriteLine($"{nmin < l} {nmax > l} {nmax == l} {nmin == l} {umax == ul} {umax > ul} {umax >= ul} {umax < ul} {nmax >= f} {nmax >= d} {umax <= f} {umax <= d}");
    Console.WriteLine($"{n < ui} {n > ui} {n == ui} {nmax > ui} {nmin < ui} {i < n} {sh < n} {c > n} {b > n} {us == n} {sb < n}");
    Console.WriteLine($"{u > ui} {u > b} {u == c} {u < us} {umax > ui}");
    Console.WriteLine($"{n & l} {n | ui} {n ^ ui} {u & ul} {u | ui} {u ^ b} {n & sb} {nmin & us} {n | c}");
    Console.WriteLine($"{n << 1} {n >> 1} {n >>> 1} {nmin >> 63} {nmin >>> 63} {u << 1} {u >> 1} {umax >>> 60} {n << sb} {n << c} {l << (int)n}");
    Console.WriteLine($"{n + 1} {n - 1} {n * 2} {n / 2} {n % 2} {u + 1} {u - 1} {u * 2} {u / 2} {u % 2} {n < 5L} {n > 5L} {u > 0} {u < 3000000000} {u + 1L} {u == 7L} {u + 4000000000L}");
    Console.WriteLine($"{1 + n} {1 - n} {2L * n} {1L < n} {0 < u} {7 == u} {7L == u} {5L - n}");
    nint? nn = 5; nint? nnull = null; nuint? un = 6;
    Console.WriteLine($"{nn + l} {nn + 1} {nnull + 1} {nn < l} {nnull < l} {nn == l} {nnull == l} {l == nnull} {nn > ui} {un + ul} {un > 0} {un + 1} {un == 6UL} {un == ui} {nn + f} {nn + m} {m + nn} {nnull + m} {nnull == m}");
    nint x = n; x += 1; x += i; x += sh; x -= b; x *= 2; x /= 3; x %= 5; x <<= 3; x >>= 1; x >>>= 1; x &= 0xFF; x |= 0x100; x ^= 3;
    Console.WriteLine(x);
    nuint y = u; y += 1; y += ui; y += b; y -= 1; y *= 2; y /= 3; y %= 5; y <<= 3; y >>= 1; y >>>= 1; y &= ui; y |= 0x100; y ^= 3;
    Console.WriteLine(y);
    long ll = 10; ll += n; ll -= n; ll *= n; ulong uu = 10; uu += u; uu *= u; uu -= u; uu |= u;
    float ff = 1; ff += n; ff *= u; double dd = 1; dd += n; dd *= u; decimal mm = 1; mm += n; mm *= u; mm -= n;
    Console.WriteLine($"{ll} {uu} {ff} {dd} {mm}");
    x = nmax; x++; Console.WriteLine(x); y = umax; y++; Console.WriteLine(y); y--; Console.WriteLine(y); --y; ++x; Console.WriteLine($"{x} {y}");
    nn++; un--; nnull++; Console.WriteLine($"{nn} {un} {nnull}");
    Console.WriteLine($"{-n} {+n} {~n} {~u} {-nmin} {n} {-nnull} {~nn}");
    try { checked { Console.WriteLine(nmax + 1); } } catch (OverflowException) { Console.WriteLine("ovf1"); }
    try { checked { Console.WriteLine(nmax + 1L); } } catch (OverflowException) { Console.WriteLine("ovf2"); }
    try { checked { Console.WriteLine(umax + 1); } } catch (OverflowException) { Console.WriteLine("ovf3"); }
    try { checked { Console.WriteLine(umax + ul); } } catch (OverflowException) { Console.WriteLine("ovf4"); }
    try { checked { Console.WriteLine(nmax * 2); } } catch (OverflowException) { Console.WriteLine("ovf5"); }
    try { checked { Console.WriteLine(nmax * l); } } catch (OverflowException) { Console.WriteLine("ovf6"); }
    try { checked { Console.WriteLine(u - 8); } } catch (OverflowException) { Console.WriteLine("ovf7"); }
    try { checked { Console.WriteLine(u - ui); } } catch (OverflowException) { Console.WriteLine("ovf8"); }
    try { checked { Console.WriteLine(nmin - 1); } } catch (OverflowException) { Console.WriteLine("ovf9"); }
    try { checked { x = nmax; x += 1; Console.WriteLine(x); } } catch (OverflowException) { Console.WriteLine("ovf10"); }
    try { checked { y = 0; y -= 1; Console.WriteLine(y); } } catch (OverflowException) { Console.WriteLine("ovf11"); }
    try { checked { x = nmax; x++; Console.WriteLine(x); } } catch (OverflowException) { Console.WriteLine("ovf12"); }
    try { checked { Console.WriteLine(nmax + ui); } } catch (OverflowException) { Console.WriteLine("ovf13"); }
    try { checked { Console.WriteLine(nmin - ui); } } catch (OverflowException) { Console.WriteLine("ovf14"); }
    unchecked { Console.WriteLine($"{nmax + 1} {umax + 1} {nmax * 2} {nmax + ui} {u - 8} {umax + ul}"); }
    Console.WriteLine($"{(float)nmax} {(double)nmax} {(decimal)nmax} {(float)nmin} {(float)umax} {(double)umax} {(decimal)umax} {(decimal)nmin} {(long)n} {(ulong)umax}");
    float fx = nmax; double dx = umax; decimal mx = umax; long lx = nmin; ulong ux = umax; float fy = umax; Console.WriteLine($"{fx} {dx} {mx} {lx} {ux} {fy}");
    float? fn = nn; double? dn = un; decimal? mn = nn; long? ln = nn; ulong? uln = un; Console.WriteLine($"{fn} {dn} {mn} {ln} {uln}");
    Console.WriteLine($"{(nmax > 5 ? nmax : 1)} {(f >= nint.MaxValue ? nint.MaxValue : (nint)1)} {Ret() - 1} {nuint.MaxValue / 2}");
    Console.WriteLine($"{n == IntPtr.Zero} {IntPtr.MaxValue > l} {l + nint.Size} {IntPtr.Size * 2} {UIntPtr.MaxValue == ul}");
    ulong cu = 5; long cl = -3; float cf = 1e30f; double cd = 2;
    Console.WriteLine($"{cl < nint.MinValue} {cl > nint.MaxValue} {cu > nuint.MaxValue} {cf >= nint.MaxValue} {cf <= nint.MinValue} {cf >= nuint.MaxValue} {cd < nint.MaxValue}");
    Console.WriteLine($"{nint.MaxValue - 1} {nint.MaxValue == IntPtr.MaxValue} {IntPtr.MaxValue > cl}");
    Console.WriteLine($"{(n > 0 ? n : l)} {(u > 0 ? u : ul)} {(n < 0 ? 1.5f : n)}");
    nint[] arr = { 1, 2, 3 }; arr[1] += 5; arr[2] <<= 2; long[] la = { 1 }; la[0] += arr[1]; Console.WriteLine($"{arr[1]} {arr[2]} {la[0]}");
    int iv = 3; iv += (int)n; Console.WriteLine(iv);
    Console.WriteLine($"{n.CompareTo(1)} {nint.Abs(n)} {nint.Max(n, 5)} {(n + 1).ToString()} {(u + 1).ToString()} {(n * 2L).GetType()} {(u * 2UL).GetType()} {(n + 1.5f).GetType()}");
  }
}
"#,
        "9223372036854775805 -9223372036854775808 -4294967298 4294967292 -12884901885 6 8 18446744073709551609 4294967302 207 65542 72\n1E+30 -7.5 -1.2 1E+30 17.5 2.8 1E+30 9.223372036854776E+18 9223372036854775809.5 1E+30 1.8446744073709552E+19 18446744073709551617.5\nFalse True False True True False True False False True True False\nTrue False False True True False False True True False True\nFalse False False True True\n-9223372036854775808 -1 -4294967294 7 4294967295 207 -128 0 -3\n-6 -2 9223372036854775806 -1 1 14 3 15 -3 -6 0\n-2 -4 -6 -1 -1 8 6 14 3 1 True False True True 8 True 4000000007\n-2 4 -6 False True True True 8\n-9223372036854775803 6  False False False False False False 5 True 7 True False 1E+30 7.5 7.5  False\n509\n261\n-30 119 -14 -14 -11\n-9223372036854775808\n0\n18446744073709551615\n-9223372036854775807 18446744073709551614\n6 5 \n3 -3 2 18446744073709551608 -9223372036854775808 -3  -7\novf1\novf2\novf3\novf4\novf5\novf6\novf7\novf8\novf9\novf10\novf11\novf12\novf13\novf14\n-9223372036854775808 0 -2 -9223372032559808514 18446744073709551615 18446744073709551614\n9.223372E+18 9.223372036854776E+18 9223372036854775807 -9.223372E+18 1.8446744E+19 1.8446744073709552E+19 18446744073709551615 -9223372036854775808 -3 18446744073709551615\n9.223372E+18 1.8446744073709552E+19 18446744073709551615 -9223372036854775808 18446744073709551615 1.8446744E+19\n6 5 6 6 5\n9223372036854775807 9223372036854775807 9223372036854775806 9223372036854775807\nFalse True -9223372036854775800 16 True\nFalse False False True False True True\n9223372036854775806 True True\n-9223372036854775808 7 1.5\n7 12 8\n0\n-1 3 5 -2 8 System.Int64 System.UInt64 System.Single\n",
    );
}

#[test]
fn extension_block_members_take_the_receivers_a_classic_extension_does() {
    check(
        "extension_block_receivers",
        r#"
using System;
using System.Collections.Generic;
using System.Linq;

interface IShape { int Sides { get; } }
struct Square : IShape { public int Sides => 4; }
class Animal { }
class Dog : Animal { }

static class Ext
{
    extension(IEnumerable<int> source) { public int Total => source.Sum(); public int Twice() => source.Sum() * 2; }
    extension(IEnumerable<object> items) { public int Count2 => items.Count(); }
    extension(IList<int> list) { public int First2 => list[0]; }
    extension(IReadOnlyList<int> list) { public int Last2 => list[list.Count - 1]; }
    extension(IShape shape) { public int Doubled => shape.Sides * 2; }
    extension(IEnumerable<char> chars) { public int Letters => chars.Count(); }
    extension(Animal animal) { public string Kind => "animal"; }
    extension<T>(IEnumerable<T> source) { public int N => source.Count(); }
    extension<T>(T value) where T : IShape { public int Sided => value.Sides + 1; }
    extension(ReadOnlySpan<int> span) { public int SpanLength => span.Length; }
    extension<T>(ReadOnlySpan<T> span) { public int Generic => span.Length; }
    extension(long number) { public long Next => number + 1; }
}

static class Program
{
    static int Through<T>(T value) where T : IShape => value.Sided;

    static void Main()
    {
        int[] numbers = [1, 2, 3];
        string[] words = ["a", "b"];
        List<int> list = [4, 5];
        Console.WriteLine(numbers.Total + " " + numbers.Twice() + " " + list.Total);
        Console.WriteLine(words.Count2 + " " + numbers.First2 + " " + numbers.Last2);
        Console.WriteLine(new Square().Doubled + " " + Through(new Square()));
        Console.WriteLine("abc".Letters + " " + new Dog().Kind);
        Console.WriteLine(numbers.N + " " + words.N + " " + list.N + " " + new Dog[] { new Dog() }.N);
        Console.WriteLine(numbers.SpanLength + " " + numbers.Generic);
        Console.WriteLine(5L.Next);
    }
}
"#,
        "6 12 9
2 1 3
8 5
3 animal
3 2 2 1
3 3
6
",
    );
}

#[test]
fn an_extension_property_wins_over_an_extension_method_of_its_name_that_is_no_nearer() {
    check(
        "extension_property_and_method_names",
        r#"
using System;
using System.Collections.Generic;
using System.Linq;
using N1;

namespace N1
{
    static class Far { extension(A a) { public int Prop => 1; public Func<int> D => () => 5; } }
}

class A { }

static class Near
{
    public static int Prop(this A a) => 2;
    public static int D(this A a) => 6;
}

static class E
{
    extension(IEnumerable<int> s) { public int Count => 5; public Func<int> Peek => () => 99; }
    extension(int n) { public int First => n; }
    extension(string t) { public int Max => 77; public Func<int> Min => () => 66; }
}

static class Program
{
    static void Main()
    {
        int[] a = { 7, 8 };
        var x = a.Count;
        Console.WriteLine(a.Count + " " + x + " " + a.Count() + " " + a.Count(v => v > 7));
        List<int> list = new() { 1, 2, 3 };
        IEnumerable<int> items = list;
        Console.WriteLine(list.Count + " " + items.Count + " " + items.Count());
        Console.WriteLine(3.First + " " + "abc".Max + " " + "abc".Min() + " " + "abc".Count());
        Func<int> peek = a.Peek;
        Console.WriteLine(a.Peek() + " " + peek() + " " + a.Peek);
        var near = new A();
        Func<int> group = near.Prop;
        Console.WriteLine(group() + " " + near.Prop() + " " + near.D());
    }
}
"#,
        "5 5 2 1
3 5 3
3 77 66 3
99 99 System.Func`1[System.Int32]
2 2 6
",
    );
}

#[test]
fn a_method_the_code_may_not_call_hides_no_extension_of_its_name() {
    check(
        "private_method_and_extension",
        r#"
using System;

class A
{
    private void M(int x) { Console.WriteLine("A.M " + x); }
    public void In(A a) { a.M(1); this.M(2); M(3); Action<int> d = a.M; d(4); }
}
class Base { private void Hid(int x) { Console.WriteLine("Base.Hid"); } }
class Der : Base { public void T() { this.Hid(1); this.Hid(1L); } }
class G
{
    private void Gen<T>(T t) { Console.WriteLine("G.Gen"); }
    private static void St(int x) { Console.WriteLine("G.St"); }
    private int Size => 1;
    public static void In(G g) { g.Gen(1); St(2); G.St(3); Console.WriteLine(g.Size); }
}

static class Ext
{
    public static void M(this A a, int x) { Console.WriteLine("Ext.M " + x); }
    public static void Hid(this Base b, long x) { Console.WriteLine("Ext.Hid"); }
    public static void Gen<T>(this G g, T t) { Console.WriteLine("Ext.Gen"); }
    extension(G) { public static void St(int x) { Console.WriteLine("Ext.St"); } }
    extension(G g) { public int Size => 100; }
}

static class Program
{
    static void Main()
    {
        var a = new A();
        a.In(a);
        a.M(5);
        Action<int> d = a.M;
        d(6);
        var f = a.M;
        f(7);
        new Der().T();
        new Base().Hid(1);
        var g = new G();
        G.In(g);
        g.Gen(1);
        g.Gen<string>("s");
        G.St(9);
        Console.WriteLine(g.Size);
    }
}
"#,
        "A.M 1
A.M 2
A.M 3
A.M 4
Ext.M 5
Ext.M 6
Ext.M 7
Ext.Hid
Ext.Hid
Ext.Hid
G.Gen
G.St
G.St
1
Ext.Gen
Ext.Gen
Ext.St
100
",
    );
}

/// An override that returns a narrower type than what it overrides (C# 9) is
/// another method to the runtime, which matches by signature: it has a slot
/// of its own, a `MethodImpl` row that puts it in the base's, and
/// `[PreserveBaseOverrides]` so that an override further down answers both.
/// Without them a call through the base ran the base's body.
#[test]
fn an_override_with_a_narrower_return_type_answers_the_base_slot() {
    check(
        "CovariantReturns",
        r#"
using System;
using System.Collections.Generic;
class B
{
    public virtual object M() => "b";
    public virtual B Self() => this;
    public virtual T G<T>(T t) => t;
    public virtual object P => "bp";
    public virtual IEnumerable<object> Seq() => new object[] { "bs" };
    public virtual object this[int i] => "bi" + i;
    public virtual object Kept() => "bk";
}
class D : B
{
    public override string M() => "d";
    public override D Self() => this;
    public override string P => "dp";
    public override IEnumerable<string> Seq() => new[] { "ds" };
    public override string this[int i] => "di" + i;
    public override object Kept() => "dk";
    public int Extra => 5;
}
class E : D
{
    public override string M() => "e";
    public override string P => "ep";
    public override E Self() => this;
    public override string this[int i] => "ei" + i;
}
abstract class Shape { public abstract Shape Clone(); public abstract object Tag { get; } }
sealed class Circle : Shape { public override Circle Clone() => new Circle(); public override string Tag => "circle"; }
class GB<T> { public virtual object Make(T t) => "gb" + t; public virtual T Same(T t) => t; }
class GD : GB<int> { public override string Make(int t) => "gd" + t; public override int Same(int t) => t + 1; }
class GD2<U> : GB<U> { public override string Make(U t) => "gd2" + t; }
class Ex : Exception { public override string Message => "exm"; public override string ToString() => "exs"; }
class Program
{
    static void Main()
    {
        D d = new E();
        string s = d.M();
        Console.WriteLine(s.Length + s);
        Console.WriteLine(d.Self().Extra);
        Console.WriteLine(new E().Self().M().ToUpper());
        B b = d;
        object o = b.M();
        Console.WriteLine(o);
        var e = new E();
        Func<string> f = e.M;
        Console.WriteLine(f());
        Func<object> fo = b.M;
        Console.WriteLine(fo());
        Console.WriteLine(e.G(3));
        Console.WriteLine(b.P + " " + d.P + " " + d.P.Length + " " + e.P);
        Console.WriteLine(b[1] + " " + d[2] + " " + d[2].Length);
        foreach (var x in b.Seq()) Console.WriteLine(x);
        foreach (string x in d.Seq()) Console.WriteLine(x.Length);
        Console.WriteLine(b.Kept() + " " + b.Self().GetType().Name + " " + new D().Self().GetType().Name);
        B plain = new D();
        Console.WriteLine(plain.M() + " " + plain.P + " " + plain[3]);
        Shape sh = new Circle();
        Console.WriteLine(sh.Clone().GetType().Name + " " + sh.Tag + " " + new Circle().Clone().Tag.Length);
        GB<int> g = new GD();
        Console.WriteLine(g.Make(1) + " " + g.Same(1) + " " + new GD().Make(2).Length);
        GB<string> g2 = new GD2<string>();
        Console.WriteLine(g2.Make("x") + " " + new GD2<int>().Make(4).Length);
        Exception ex = new Ex();
        Console.WriteLine(ex.Message + " " + ex);
    }
}
"#,
        "1e
5
E
e
e
e
3
ep ep 2 ep
ei1 ei2 3
ds
2
dk E D
d dp di3
Circle circle 6
gd1 2 3
gd2x 4
exm exs
",
    );
}
