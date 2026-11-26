//! End-to-end tests: C# in, a running program out.
//!
//! An emitter can only really be tested by running what it produces. Every
//! test here compiles a program, writes the assembly to a temporary directory
//! and executes it with the .NET host, then compares the output against what
//! `csc` would have produced for the same source.
//!
//! When no host is installed the tests still compile the program and assert
//! that emission succeeded, and say in their output that they could not run
//! it. Set `RUSTLYN_DOTNET` to a `dotnet` executable to point them at one.

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

/// A directory of this test's own, so tests do not tread on each other.
fn scratch(name: &str) -> PathBuf {
    let directory = std::env::temp_dir().join(format!("rustlyn-emit-{name}"));
    let _ = std::fs::remove_dir_all(&directory);
    std::fs::create_dir_all(&directory).expect("a temporary directory should be creatable");
    directory
}

/// Compiles `source` and writes the assembly, failing the test on any
/// error or on anything the backend cannot emit. A warning (a switch
/// expression left open on purpose, `==` without `Equals`) is not one.
fn build(name: &str, source: &str) -> PathBuf {
    let compilation = Compilation::create(vec![parse(SourceText::new("Program.cs", source))]);
    let diagnostics: Vec<String> = compilation
        .source_diagnostics()
        .into_iter()
        .filter(|entry| entry.diagnostic.is_error())
        .map(|entry| compilation.render(entry))
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

    let emitted = rustlyn_emit::emit(&compilation, name)
        .unwrap_or_else(|error| panic!("{name} could not be emitted: {error}"));

    let directory = scratch(name);
    let assembly = directory.join(format!("{name}.dll"));
    std::fs::write(&assembly, &emitted.assembly).expect("the assembly should be writable");
    std::fs::write(
        directory.join(format!("{name}.runtimeconfig.json")),
        &emitted.runtime_config,
    )
    .expect("the runtime configuration should be writable");
    assembly
}

/// Runs an assembly and returns everything it printed.
fn run(assembly: &Path) -> Option<String> {
    let host = host()?;
    // On macOS .NET 10 formats by the region the system settings name
    // (`1,5` under a Georgian one) unless the environment names a locale;
    // the expected output is written in en-US.
    let mut command = Command::new(&host);
    if cfg!(target_os = "macos") && std::env::var_os("LC_ALL").is_none() {
        command.env("LC_ALL", "en_US.UTF-8");
    }
    let output = output_within(command.arg(assembly));
    let stdout = String::from_utf8_lossy(&output.stdout).replace("\r\n", "\n");
    assert!(
        output.status.success(),
        "{} failed: {}{}",
        assembly.display(),
        stdout,
        String::from_utf8_lossy(&output.stderr)
    );
    Some(stdout)
}

/// Compiles, runs and compares. The comparison is skipped, loudly, when there
/// is no host to run on.
#[track_caller]
fn check(name: &str, source: &str, expected: &str) {
    let assembly = build(name, source);
    match run(&assembly) {
        Some(output) => assert_eq!(output, expected, "{name} printed the wrong thing"),
        None => println!(
            "note: {name} was emitted but not run; no .NET host was found \
             (set RUSTLYN_DOTNET to one)"
        ),
    }
}

#[test]
fn hello_world() {
    check(
        "Hello",
        r#"
using System;
class Hello
{
    static void Main() { Console.WriteLine("hello"); }
}
"#,
        "hello\n",
    );
}

#[test]
fn arithmetic_and_locals() {
    check(
        "Arithmetic",
        r"
using System;
class Arithmetic
{
    static void Main()
    {
        int a = 7;
        int b = 3;
        Console.WriteLine(a + b);
        Console.WriteLine(a - b);
        Console.WriteLine(a * b);
        Console.WriteLine(a / b);
        Console.WriteLine(a % b);
        Console.WriteLine(-a);
        Console.WriteLine(a > b);
        Console.WriteLine(a <= b);
        Console.WriteLine(a == 7 && b != 3);
        Console.WriteLine(a == 7 || b != 3);
    }
}
",
        "10\n4\n21\n2\n1\n-7\nTrue\nFalse\nFalse\nTrue\n",
    );
}

#[test]
fn control_flow() {
    check(
        "Control",
        r"
using System;
class Control
{
    static void Main()
    {
        int total = 0;
        for (int i = 0; i < 10; i++)
        {
            if (i % 3 == 0) { continue; }
            if (i > 7) { break; }
            total += i;
        }
        Console.WriteLine(total);

        int n = 5;
        while (n > 0) { n--; }
        Console.WriteLine(n);

        do { n += 4; } while (n < 10);
        Console.WriteLine(n);
    }
}
",
        // 1 + 2 + 4 + 5 + 7: the multiples of three are skipped and the loop
        // stops at eight.
        "19\n0\n12\n",
    );
}

#[test]
fn arrays_and_foreach() {
    check(
        "Arrays",
        r"
using System;
class Arrays
{
    static int Sum(int[] values)
    {
        int total = 0;
        foreach (int value in values) { total += value; }
        return total;
    }

    static void Main()
    {
        int[] numbers = new int[] { 3, 1, 4, 1, 5 };
        Console.WriteLine(numbers.Length);
        Console.WriteLine(numbers[2]);
        numbers[0] = 10;
        Console.WriteLine(Sum(numbers));

        int[] empty = new int[3];
        Console.WriteLine(Sum(empty));
    }
}
",
        "5\n4\n21\n0\n",
    );
}

#[test]
fn classes_fields_and_constructors() {
    check(
        "Classes",
        r#"
using System;
class Point
{
    private int x;
    private int y;
    public Point(int x, int y) { this.x = x; this.y = y; }
    public int Sum() { return x + y; }
}
class Classes
{
    static void Main()
    {
        Point p = new Point(3, 4);
        Console.WriteLine(p.Sum());
    }
}
"#,
        "7\n",
    );
}

#[test]
fn inheritance_dispatches_on_the_run_time_type() {
    check(
        "Virtual",
        r#"
using System;
class Shape
{
    public virtual string Describe() { return "shape"; }
}
class Square : Shape
{
    public override string Describe() { return "square"; }
}
class Virtual
{
    static void Main()
    {
        Shape s = new Square();
        Console.WriteLine(s.Describe());
    }
}
"#,
        "square\n",
    );
}

#[test]
fn a_base_initializer_runs_the_base_constructor() {
    check(
        "BaseCall",
        r#"
using System;
class Animal
{
    private string name;
    public Animal(string name) { this.name = name; }
    public string Name() { return name; }
}
class Dog : Animal
{
    public Dog() : base("dog") { }
}
class BaseCall
{
    static void Main() { Console.WriteLine(new Dog().Name()); }
}
"#,
        "dog\n",
    );
}

#[test]
fn field_initializers_run_before_the_constructor_body() {
    check(
        "Initializers",
        r"
using System;
class Holder
{
    public int Value = 7;
    public Holder() { Value = Value + 1; }
}
class Initializers
{
    static int Count = 41;
    static void Main()
    {
        Console.WriteLine(new Holder().Value);
        Console.WriteLine(Count + 1);
    }
}
",
        "8\n42\n",
    );
}

#[test]
fn automatic_properties_get_a_backing_field() {
    check(
        "Properties",
        r"
using System;
class Counter
{
    public int Value { get; set; }
    public void Bump() { Value = Value + 1; }
}
class Properties
{
    static void Main()
    {
        Counter c = new Counter();
        c.Bump();
        c.Bump();
        Console.WriteLine(c.Value);
        c.Value = 40;
        Console.WriteLine(c.Value + 2);
    }
}
",
        "2\n42\n",
    );
}

#[test]
fn strings_concatenate_and_compare_by_value() {
    check(
        "Strings",
        r#"
using System;
class Strings
{
    static void Main()
    {
        string a = "ab";
        string b = "a" + "b";
        Console.WriteLine(a == b);
        Console.WriteLine(a != b);
        Console.WriteLine("n = " + 41);
        Console.WriteLine($"{a} has {a.Length} characters");
    }
}
"#,
        "True\nFalse\nn = 41\nab has 2 characters\n",
    );
}

#[test]
fn a_conditional_evaluates_only_one_branch() {
    check(
        "Conditional",
        r#"
using System;
class Conditional
{
    static int Boom() { throw new Exception("should not run"); }
    static void Main()
    {
        int n = 2;
        Console.WriteLine(n > 1 ? "big" : "small");
        Console.WriteLine(n > 1 || Boom() == 0);
    }
}
"#,
        "big\nTrue\n",
    );
}

#[test]
fn patterns_in_a_switch_expression() {
    check(
        "Patterns",
        r#"
using System;
class Patterns
{
    static string Describe(object o) => o switch
    {
        int n when n > 100 => "big",
        int n => "int " + n,
        string s => "string of " + s.Length,
        null => "null",
        _ => "other",
    };

    static void Main()
    {
        Console.WriteLine(Describe(7));
        Console.WriteLine(Describe(700));
        Console.WriteLine(Describe("abc"));
        Console.WriteLine(Describe(null));
        Console.WriteLine(Describe(1.5));
    }
}
"#,
        "int 7\nbig\nstring of 3\nnull\nother\n",
    );
}

#[test]
fn relational_and_combined_patterns_in_a_switch_statement() {
    check(
        "Grades",
        r#"
using System;
class Grades
{
    static string Grade(int score)
    {
        switch (score)
        {
            case 100: return "perfect";
            case > 89: return "A";
            case > 79 and <= 89: return "B";
            case < 0:
            case > 100: return "impossible";
            default: return "C";
        }
    }

    static void Main()
    {
        Console.WriteLine(Grade(100));
        Console.WriteLine(Grade(95));
        Console.WriteLine(Grade(85));
        Console.WriteLine(Grade(-1));
        Console.WriteLine(Grade(50));
    }
}
"#,
        "perfect\nA\nB\nimpossible\nC\n",
    );
}

#[test]
fn is_patterns_bind_and_narrow() {
    check(
        "IsPattern",
        r#"
using System;
class IsPattern
{
    static void Main()
    {
        object x = "hi";
        if (x is string s) { Console.WriteLine(s.Length); }
        Console.WriteLine(x is int);
        Console.WriteLine(x is not null);
        Console.WriteLine(x is string or int);
    }
}
"#,
        "2\nFalse\nTrue\nTrue\n",
    );
}

#[test]
fn continue_inside_a_switch_reaches_the_loop_around_it() {
    check(
        "SwitchLoop",
        r#"
using System;
class SwitchLoop
{
    static void Main()
    {
        for (int i = 0; i < 4; i++)
        {
            switch (i)
            {
                case 1: continue;
                case 2: break;
                default: Console.Write("d"); break;
            }
            Console.Write(i);
        }
        Console.WriteLine();
    }
}
"#,
        "d02d3\n",
    );
}

#[test]
fn an_unmatched_switch_expression_throws_what_csc_throws() {
    let assembly = build(
        "Exhaustive",
        r"
class Exhaustive
{
    static int Pick(int n) => n switch { 1 => 10 };
    static void Main() { Pick(2); }
}
",
    );
    let Some(host) = host() else {
        println!("note: Exhaustive was emitted but not run; no .NET host was found");
        return;
    };
    let output = output_within(std::process::Command::new(host).arg(&assembly));
    assert!(!output.status.success(), "the program should have thrown");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("SwitchExpressionException"),
        "unexpected failure: {stderr}"
    );
}

#[test]
fn try_catch_finally_in_the_order_the_runtime_runs_them() {
    check(
        "Handlers",
        r#"
using System;
class Handlers
{
    static int Risky(int n)
    {
        try
        {
            if (n == 0) { throw new InvalidOperationException("zero"); }
            if (n < 0) { throw new ArgumentException("negative"); }
            return 100 / n;
        }
        catch (ArgumentException e)
        {
            Console.WriteLine("argument: " + e.Message);
            return -1;
        }
        catch (Exception e) when (e.Message == "zero")
        {
            Console.WriteLine("filtered: " + e.Message);
            return -2;
        }
        catch
        {
            Console.WriteLine("other");
            return -3;
        }
        finally
        {
            Console.WriteLine("finally " + n);
        }
    }

    static void Main()
    {
        Console.WriteLine(Risky(5));
        Console.WriteLine(Risky(0));
        Console.WriteLine(Risky(-2));
    }
}
"#,
        // The `finally` runs before the value reaches the caller, which is why
        // each "finally n" comes out before the number it belongs to.
        "finally 5\n20\nfiltered: zero\nfinally 0\n-2\nargument: negative\nfinally -2\n-1\n",
    );
}

#[test]
fn leaving_a_protected_region_runs_its_finally() {
    check(
        "Leaving",
        r#"
using System;
class Leaving
{
    static void Main()
    {
        for (int i = 0; i < 4; i++)
        {
            try
            {
                if (i == 1) { continue; }
                if (i == 2) { break; }
                Console.Write("b" + i);
            }
            finally { Console.Write("f" + i); }
        }
        Console.WriteLine();

        try
        {
            try { throw new Exception("inner"); }
            finally { Console.WriteLine("inner finally"); }
        }
        catch (Exception e) { Console.WriteLine("caught " + e.Message); }
    }
}
"#,
        "b0f0f1f2\ninner finally\ncaught inner\n",
    );
}

#[test]
fn an_interface_dispatches_to_whatever_implements_it() {
    check(
        "Interfaces",
        r#"
using System;
interface IShape
{
    int Area();
    string Name();
}
class Square : IShape
{
    private int side;
    public Square(int side) { this.side = side; }
    public int Area() { return side * side; }
    public string Name() { return "square"; }
}
class Circle : IShape
{
    public int Area() { return 3; }
    public string Name() { return "circle"; }
}
class Interfaces
{
    static void Report(IShape s) { Console.WriteLine(s.Name() + " " + s.Area()); }
    static void Main()
    {
        Report(new Square(4));
        Report(new Circle());
        IShape[] all = new IShape[] { new Square(2), new Circle() };
        int total = 0;
        foreach (IShape s in all) { total += s.Area(); }
        Console.WriteLine(total);
        object o = new Square(1);
        Console.WriteLine(o is IShape);
    }
}
"#,
        "square 16\ncircle 3\n7\nTrue\n",
    );
}

#[test]
fn an_enum_carries_its_values_in_metadata() {
    check(
        "Enums",
        r#"
using System;
enum Colour { Red, Green = 4, Blue, Alias = Green }
enum Flags { None = 0, A = 1, B = 2, Both = A | B }
class Enums
{
    const int Limit = 3 * 4;

    static string Name(Colour c)
    {
        switch (c)
        {
            case Colour.Red: return "red";
            case Colour.Green: return "green";
            case Colour.Blue: return "blue";
            default: return "?";
        }
    }

    static void Main()
    {
        Console.WriteLine(Name(Colour.Red));
        Console.WriteLine(Name(Colour.Blue));
        Console.WriteLine(Name(Colour.Alias));
        // The runtime finds the names in the metadata this wrote.
        Console.WriteLine(Colour.Green);
        Console.WriteLine(Flags.Both);
        Console.WriteLine((int)Colour.Blue);
        Console.WriteLine(Limit);
    }
}
"#,
        "red\nblue\ngreen\nGreen\nBoth\n5\n12\n",
    );
}

#[test]
fn a_struct_is_copied_and_mutated_in_place() {
    check(
        "Structs",
        r"
using System;
struct Point
{
    public int X;
    public int Y;
    public Point(int x, int y) { X = x; Y = y; }
    public int Sum() { return X + Y; }
    public void Shift(int dx) { X = X + dx; }
}
class Structs
{
    static int Total(Point p) { return p.X + p.Y; }
    static void Main()
    {
        Point a = new Point(3, -4);
        Console.WriteLine(a.Sum());
        Console.WriteLine(Total(a));
        a.X = 10;
        Console.WriteLine(a.X + a.Y);
        // A method on a struct works on the struct, not on a copy of it.
        a.Shift(5);
        Console.WriteLine(a.X);
        Console.WriteLine(new Point().X);
        // Assigning a struct copies it, so `c` and `a` go their own ways.
        Point c = a;
        c.X = 999;
        Console.WriteLine(a.X);
        object boxed = a;
        Console.WriteLine(boxed is Point);
    }
}
",
        "-1\n-1\n6\n15\n0\n15\nTrue\n",
    );
}

#[test]
fn using_disposes_in_reverse_and_on_the_way_out() {
    check(
        "Disposal",
        r#"
using System;
class Resource : IDisposable
{
    private string name;
    public Resource(string name) { this.name = name; Console.WriteLine("open " + name); }
    public void Use() { Console.WriteLine("use " + name); }
    public void Dispose() { Console.WriteLine("close " + name); }
}
class Disposal
{
    static void Tail()
    {
        using Resource e = new Resource("e");
        Console.WriteLine("end of tail");
    }

    static void Main()
    {
        using (Resource b = new Resource("b"))
        using (Resource c = new Resource("c"))
        {
            b.Use();
        }

        try
        {
            using (Resource d = new Resource("d")) { throw new Exception("boom"); }
        }
        catch (Exception e) { Console.WriteLine("caught " + e.Message); }

        Tail();
    }
}
"#,
        "open b\nopen c\nuse b\nclose c\nclose b\nopen d\nclose d\ncaught boom\n\
         open e\nend of tail\nclose e\n",
    );
}

/// Programs that both backends can handle, run both ways.
#[test]
fn generic_types() {
    check(
        "Generic",
        r#"
using System;
interface INamed { string Name(); }
class Cell<T> : INamed
{
    private T value;
    public Cell(T value) { this.value = value; }
    public T Value { get { return value; } }
    public string Name() { return "cell"; }
    public Cell<T> Copy() { return new Cell<T>(value); }
}
class Pair<A, B>
{
    public A First;
    public B Second;
    public Pair(A first, B second) { First = first; Second = second; }
}
class Generic
{
    static void Main()
    {
        Cell<int> a = new Cell<int>(5);
        Console.WriteLine(a.Value);
        Console.WriteLine(a.Name());
        Console.WriteLine(a.Copy().Value);

        // A construction can be an argument to another construction.
        Cell<Cell<int>> nested = new Cell<Cell<int>>(a);
        Console.WriteLine(nested.Value.Value);

        INamed named = a;
        Console.WriteLine(named.Name());

        Pair<string, int> pair = new Pair<string, int>("two", 2);
        Console.WriteLine(pair.First + " " + pair.Second);
    }
}
"#,
        "5\ncell\n5\n5\ncell\ntwo 2\n",
    );
}

#[test]
fn indexers() {
    check(
        "Indexer",
        r#"
using System;
using System.Collections.Generic;
class Indexer
{
    static void Main()
    {
        string text = "hello";
        Console.WriteLine(text[1]);

        List<int> numbers = new List<int>();
        numbers.Add(1);
        numbers.Add(2);
        numbers[0] = 10;
        // A compound assignment reads and writes the same element, which is
        // what makes an indexer more than two independent calls.
        numbers[1] += 5;
        Console.WriteLine(numbers[0]);
        Console.WriteLine(numbers[1]);
        Console.WriteLine(numbers.Count);

        Dictionary<string, int> ages = new Dictionary<string, int>();
        ages["ann"] = 30;
        ages["bob"] = 41;
        ages["ann"] = 31;
        Console.WriteLine(ages["ann"] + ages["bob"]);
        Console.WriteLine(ages.Count);
    }
}
"#,
        "e\n10\n7\n2\n72\n2\n",
    );
}

#[test]
fn ref_and_out_parameters() {
    check(
        "ByRef",
        r#"
using System;
struct Pair { public int A; public int B; }
class Holder { public int N; }
record Point(int X, int Y);
class ByRef
{
    static void Split(int total, out int half, out int rest)
    {
        half = total / 2;
        rest = total - half;
    }
    static void Bump(ref int value) { value = value + 1; }
    // A `ref` parameter passed on stays pointing where it did.
    static void BumpTwice(ref int value) { Bump(ref value); Bump(ref value); }
    static void Swap(ref string a, ref string b) { string t = a; a = b; b = t; }
    // A `ref` parameter of a value type is already an address, so writing a
    // field of it writes the caller's copy.
    static void Fill(ref Pair p) { p.A = 1; p.B = 2; }

    static void Main()
    {
        int a;
        int b;
        Split(7, out a, out b);
        Console.WriteLine(a + " " + b);

        int n = 5;
        Bump(ref n);
        BumpTwice(ref n);
        Console.WriteLine(n);

        string x = "left";
        string y = "right";
        Swap(ref x, ref y);
        Console.WriteLine(x + " " + y);

        // A field and an array element are variables too.
        Holder h = new Holder();
        h.N = 10;
        Bump(ref h.N);
        Console.WriteLine(h.N);

        int[] numbers = new int[3];
        numbers[1] = 20;
        Bump(ref numbers[1]);
        Console.WriteLine(numbers[1]);

        Pair p = new Pair();
        Fill(ref p);
        Console.WriteLine(p.A + " " + p.B);

        int parsed;
        Console.WriteLine(Int32.TryParse("42", out parsed) + " " + parsed);
        Console.WriteLine(Int32.TryParse("no", out parsed) + " " + parsed);

        // A record hands its parts back the same way.
        Point point = new Point(3, 4);
        int px;
        int py;
        point.Deconstruct(out px, out py);
        Console.WriteLine(px + " " + py);
    }
}
"#,
        "3 4\n8\nright left\n11\n21\n1 2\nTrue 42\nFalse 0\n3 4\n",
    );
}

#[test]
fn records() {
    check(
        "Record",
        r#"
using System;
record Point(int X, int Y);
record Named(string Who, int Age);
// A record inside a record compares by value all the way down, because
// `object.Equals` reaches the inner record's own `Equals`.
record Wrapper(Point Inner, string Tag);
record Empty();
class Record
{
    static void Main()
    {
        Point p = new Point(1, 2);
        Console.WriteLine(p.X + " " + p.Y);
        Console.WriteLine(p);
        Console.WriteLine(p == new Point(1, 2));
        Console.WriteLine(p != new Point(1, 3));
        Console.WriteLine(p.Equals(new Point(1, 2)));
        Console.WriteLine(p.GetHashCode() == new Point(1, 2).GetHashCode());

        Console.WriteLine(new Named("ann", 30));
        Console.WriteLine(new Named("ann", 30) == new Named("bob", 30));

        Wrapper w = new Wrapper(new Point(1, 2), "t");
        Console.WriteLine(w);
        Console.WriteLine(w == new Wrapper(new Point(1, 2), "t"));
        Console.WriteLine(w == new Wrapper(new Point(9, 2), "t"));

        Console.WriteLine(new Empty());

        Point nothing = null;
        Console.WriteLine(nothing == null);
        Console.WriteLine(p == nothing);
        Console.WriteLine(((object)p) is Point);
    }
}
"#,
        "1 2\nPoint { X = 1, Y = 2 }\nTrue\nTrue\nTrue\nTrue\n\
         Named { Who = ann, Age = 30 }\nFalse\n\
         Wrapper { Inner = Point { X = 1, Y = 2 }, Tag = t }\nTrue\nFalse\n\
         Empty { }\nTrue\nFalse\nTrue\n",
    );
}

#[test]
fn user_defined_operators() {
    check(
        "Operator",
        r#"
using System;
struct Money
{
    public int Cents;
    public Money(int cents) { Cents = cents; }
    public static Money operator +(Money a, Money b) { return new Money(a.Cents + b.Cents); }
    public static Money operator -(Money a, Money b) { return new Money(a.Cents - b.Cents); }
    public static bool operator ==(Money a, Money b) { return a.Cents == b.Cents; }
    public static bool operator !=(Money a, Money b) { return a.Cents != b.Cents; }
    public static bool operator <(Money a, Money b) { return a.Cents < b.Cents; }
    public static bool operator >(Money a, Money b) { return a.Cents > b.Cents; }
    public override string ToString() { return Cents + "c"; }
}
class Operator
{
    static void Main()
    {
        Money a = new Money(30);
        Money b = new Money(12);
        Console.WriteLine(a + b);
        Console.WriteLine(a - b);
        Console.WriteLine(a == b);
        Console.WriteLine(a != b);
        Console.WriteLine(a < b);
        Console.WriteLine(a > b);
        Console.WriteLine(a == new Money(30));
    }
}
"#,
        "42c\n18c\nFalse\nTrue\nFalse\nTrue\nTrue\n",
    );
}

#[test]
fn lambdas() {
    check(
        "Lambda",
        r#"
using System;
delegate int Op(int x);
delegate string Show();
delegate void Act();
class Lambda
{
    private int offset = 100;
    static int Apply(Op f, int v) { return f(v); }
    // Reads `this`, so the method it becomes is an instance method and the
    // delegate is made over `this`.
    public Op Shifter() { return x => x + offset; }

    static void Main()
    {
        Op twice = x => x * 2;
        Console.WriteLine(twice(21));
        Console.WriteLine(Apply(x => x + 1, 41));

        Show hello = () => "hi";
        Console.WriteLine(hello());

        Op block = x => { int y = x + 1; return y * y; };
        Console.WriteLine(block(3));

        Console.WriteLine(new Lambda().Shifter()(5));

        Act nothing = () => { };
        nothing();
        Console.WriteLine("done");
    }
}
"#,
        "42\n42\nhi\n16\n105\ndone\n",
    );
}

#[test]
fn lambdas_that_capture() {
    check(
        "Capture",
        r#"
using System;
delegate int Op(int x);
delegate void Act();
delegate string Show();
class Capture
{
    private int seed = 100;
    // Captures `this` and a local at once, so the display class gets a
    // `<>4__this` field alongside the local's.
    public Show Both(string tag)
    {
        int n = 5;
        return () => tag + (seed + n);
    }
    // Captures a parameter, which has to outlive the method that took it.
    static Op Adder(int by) { return x => x + by; }
    // Two lambdas over one variable share it, so both see every write.
    static void Shared()
    {
        int total = 0;
        Act add = () => { total = total + 3; };
        Op read = x => total * x;
        add();
        add();
        Console.WriteLine(read(2));
    }
    static Op Nested(int outer)
    {
        return x => {
            Op inner = y => y + outer;
            return inner(x) * 2;
        };
    }
    static void Main()
    {
        Console.WriteLine(Adder(7)(1));
        Shared();
        Console.WriteLine(new Capture().Both("v=")());
        Console.WriteLine(Nested(10)(1));

        // A `for` variable is one variable, so both delegates see its last
        // value — which is what C# says for `for`, unlike `foreach`.
        Op[] fs = new Op[2];
        int i = 0;
        for (i = 0; i < 2; i++) { fs[i] = x => x + i; }
        Console.WriteLine(fs[0](0) + " " + fs[1](0));
    }
}
"#,
        "8\n12\nv=105\n22\n2 2\n",
    );
}

#[test]
fn a_compound_assignment_to_a_field_leaves_nothing_on_the_stack() {
    // `stfld` takes the object as well as the value. Counting it as one pop
    // made the stack look like it grew each time round the loop, and the
    // emitter then never finished working out `.maxstack`.
    check(
        "Compound",
        r#"
using System;
class Box { public int n; }
class Compound
{
    static void Main()
    {
        Box b = new Box();
        for (int i = 0; i < 3; i++) { b.n += 1; }
        b.n++;
        Console.WriteLine(b.n);
    }
}
"#,
        "4\n",
    );
}

#[test]
fn delegates() {
    check(
        "Delegate",
        r#"
using System;
delegate int Op(int x);
delegate string Namer();
class Shape
{
    public virtual string Name() { return "shape"; }
}
class Square : Shape
{
    public override string Name() { return "square"; }
}
class Delegate
{
    static int Apply(Op f, int value) { return f(value); }
    static Op Chosen(bool negate) { return negate ? new Op(Neg) : new Op(Dbl); }
    static int Neg(int x) { return -x; }
    static int Dbl(int x) { return x + x; }
    int offset = 10;
    int Shift(int x) { return x + offset; }
    static Op held;

    static void Main()
    {
        // A method group reaching a delegate, by assignment and by `new`.
        Op f = Dbl;
        Console.WriteLine(f(21));
        Console.WriteLine(Apply(Neg, 3));
        // The result of a call is a delegate too, and can be invoked.
        Console.WriteLine(Chosen(true)(4));
        // So is a field.
        held = Neg;
        Console.WriteLine(held(7));

        // An instance method carries its receiver.
        Delegate instance = new Delegate();
        Op shift = instance.Shift;
        Console.WriteLine(shift(1));

        // A virtual target is settled when the delegate is made, from the
        // receiver it is made with.
        Shape s = new Square();
        Namer n = s.Name;
        Console.WriteLine(n());

        Shout say = Console.WriteLine;
        say("said");
    }
}
delegate void Shout(string text);
"#,
        "42\n-3\n-4\n-7\n11\nsquare\nsaid\n",
    );
}

#[test]
fn foreach_over_an_enumerator() {
    check(
        "Enumerate",
        r#"
using System;
using System.Collections.Generic;
// A type that implements nothing: C# looks for `GetEnumerator`, `MoveNext`
// and `Current` by name, not for an interface.
class Countdown
{
    private int from;
    public Countdown(int from) { this.from = from; }
    public CountdownEnumerator GetEnumerator() { return new CountdownEnumerator(from); }
}
class CountdownEnumerator
{
    private int next;
    public CountdownEnumerator(int from) { next = from + 1; }
    public int Current { get { return next; } }
    public bool MoveNext() { next = next - 1; return next > 0; }
}
class Enumerate
{
    static int SumUntilFive(List<int> items)
    {
        int total = 0;
        foreach (int item in items)
        {
            // `continue` and `break` both have to leave the protected region
            // the enumerator's `finally` sits in.
            if (item == 3) { continue; }
            if (item > 5) { break; }
            total += item;
        }
        return total;
    }
    static int FirstNegative(List<int> items)
    {
        // A `return` out of the loop is the same problem again.
        foreach (int item in items)
        {
            if (item < 0) { return item; }
        }
        return 0;
    }
    static void Main()
    {
        List<int> numbers = new List<int>();
        numbers.Add(1);
        numbers.Add(3);
        numbers.Add(4);
        numbers.Add(9);
        numbers.Add(2);
        Console.WriteLine(SumUntilFive(numbers));

        List<int> mixed = new List<int>();
        mixed.Add(4);
        mixed.Add(-7);
        Console.WriteLine(FirstNegative(mixed));

        foreach (int n in new Countdown(3)) { Console.Write(n); }
        Console.WriteLine();

        List<string> words = new List<string>();
        words.Add("a");
        words.Add("b");
        string joined = "";
        foreach (var word in words) { joined = joined + word; }
        Console.WriteLine(joined);
    }
}
"#,
        "5\n-7\n321\nab\n",
    );
}

#[test]
fn generic_methods() {
    check(
        "GenericMethod",
        r#"
using System;
using System.Collections.Generic;
class Pair<A, B>
{
    public A First;
    public B Second;
    public Pair(A first, B second) { First = first; Second = second; }
    // A generic method on a generic type: `!0` and `!!0` in one signature.
    public Pair<A, C> With<C>(C value) { return new Pair<A, C>(First, value); }
}
class Util
{
    public static T Pick<T>(T[] items, int index) { return items[index]; }
    public static List<T> Wrap<T>(T value)
    {
        List<T> list = new List<T>();
        list.Add(value);
        return list;
    }
    public T Instance<T>(T value) { return value; }
    public static T Twice<T>(T value) { return Pick<T>(new T[] { value, value }, 1); }
}
class GenericMethod
{
    static void Main()
    {
        // Inferred from an array, so `T` comes out of the element type.
        int[] numbers = { 10, 20, 30 };
        Console.WriteLine(Util.Pick(numbers, 1));
        string[] words = { "a", "b" };
        Console.WriteLine(Util.Pick(words, 0));

        List<string> wrapped = Util.Wrap("only");
        Console.WriteLine(wrapped.Count + " " + wrapped[0]);

        Console.WriteLine(new Util().Instance<string>("inst"));
        Console.WriteLine(Util.Twice(7));

        Pair<int, string> p = new Pair<int, string>(1, "one");
        Pair<int, bool> q = p.With(true);
        Console.WriteLine(q.First + " " + q.Second);
    }
}
"#,
        "20\na\n1 only\ninst\n7\n1 True\n",
    );
}

#[test]
fn a_try_at_the_end_of_a_method_still_returns() {
    // The `leave` at the end of a `catch` targets the instruction after the
    // whole statement — and there is none, unless a `ret` is put there. Nothing
    // in the stream says so: `leave` ends flow, so the body looks finished.
    check(
        "Trailing",
        r#"
using System;
class Trailing
{
    static void Main()
    {
        try { throw new ArgumentException("bad"); }
        catch (InvalidOperationException) { Console.WriteLine("wrong"); }
        catch (ArgumentException e) { Console.WriteLine("right " + e.Message); }
    }
}
"#,
        "right bad\n",
    );
}

#[test]
fn accessors_with_bodies() {
    check(
        "Accessor",
        r#"
using System;
class Temp
{
    private int celsius;
    public int Celsius
    {
        get { return celsius; }
        set
        {
            // `value` is a parameter nobody writes, and a setter body has no
            // other way to name what it was given.
            if (value < -273) { throw new ArgumentException("too cold"); }
            celsius = value;
        }
    }
    public int Fahrenheit => celsius * 9 / 5 + 32;
    public static string Unit { get { return "C"; } }
}
class Accessor
{
    static void Main()
    {
        Temp temp = new Temp();
        temp.Celsius = 100;
        Console.WriteLine(temp.Celsius + " " + temp.Fahrenheit + Temp.Unit);
        try { temp.Celsius = -300; }
        catch (ArgumentException e) { Console.WriteLine("caught " + e.Message); }
        Console.WriteLine(temp.Celsius);
    }
}
"#,
        "100 212C\ncaught too cold\n100\n",
    );
}

#[test]
fn a_declared_indexer() {
    check(
        "Bag",
        r#"
using System;
class Bag
{
    private int[] items = new int[4];
    private int writes;
    public int this[int i]
    {
        get { return items[i]; }
        set { items[i] = value; writes = writes + 1; }
    }
    public int Writes { get { return writes; } }
}
class Table<T>
{
    private T[] slots = new T[3];
    public T this[int i]
    {
        get { return slots[i]; }
        set { slots[i] = value; }
    }
}
class Program
{
    static void Main()
    {
        Bag b = new Bag();
        b[1] = 5;
        Console.WriteLine(b[1]);
        b[1] += 3;
        Console.WriteLine(b[1] + " after " + b.Writes + " writes");

        // An indexer on a generic type: the accessors are a `MemberRef` under
        // the construction's `TypeSpec`.
        Table<string> t = new Table<string>();
        t[0] = "a";
        t[2] = "c";
        Console.WriteLine(t[0] + t[2]);
    }
}
"#,
        "5\n8 after 2 writes\nac\n",
    );
}

const SHARED: &[(&str, &str)] = &[
    (
        "Agree1",
        r#"
using System;
class Agree1
{
    static string Describe(object o) => o switch
    {
        int n when n > 100 => "big",
        int n => "int " + n,
        string s => "string of " + s.Length,
        null => "null",
        _ => "other",
    };
    static void Main()
    {
        Console.WriteLine(Describe(7));
        Console.WriteLine(Describe(700));
        Console.WriteLine(Describe("abc"));
        Console.WriteLine(Describe(null));
    }
}
"#,
    ),
    (
        "Agree2",
        r#"
using System;
class Agree2
{
    static void Main()
    {
        for (int i = 0; i < 4; i++)
        {
            switch (i)
            {
                case 1: continue;
                case 2: break;
                default: Console.Write("d"); break;
            }
            Console.Write(i);
        }
        Console.WriteLine();
    }
}
"#,
    ),
    (
        "Agree4",
        r#"
using System;
class Handle : IDisposable
{
    public void Dispose() { Console.WriteLine("closed"); }
}
class Agree4
{
    static void Main()
    {
        using (Handle h = new Handle()) { Console.WriteLine("working"); }
    }
}
"#,
    ),
    (
        "Agree3",
        r#"
using System;
class Shape
{
    public virtual string Name() { return "shape"; }
    public int Size = 2;
}
class Square : Shape
{
    public override string Name() { return "square"; }
}
class Agree3
{
    static void Main()
    {
        Shape s = new Square();
        Console.WriteLine(s.Name() + " " + s.Size);
        int[] values = { 3, 1, 4 };
        int total = 0;
        foreach (int v in values) { total += v; }
        Console.WriteLine(total);
        try { throw new Exception("boom"); }
        catch (Exception e) { Console.WriteLine("caught " + e.Message); }
        finally { Console.WriteLine("done"); }
    }
}
"#,
    ),
    (
        "Agree4",
        r#"
using System;
using System.Collections.Generic;
class Box<T>
{
    private T item;
    public Box(T item) { this.item = item; }
    public T Item { get { return item; } }
}
class Agree4
{
    static void Main()
    {
        Box<string> box = new Box<string>("wrapped");
        Console.WriteLine(box.Item);
        Box<int> counted = new Box<int>(3);
        Console.WriteLine(counted.Item + 1);

        List<string> words = new List<string>();
        words.Add("one");
        words.Add("two");
        words[0] = "ONE";
        Console.WriteLine(words[0] + words[1] + words.Count);

        Dictionary<string, int> scores = new Dictionary<string, int>();
        scores["a"] = 1;
        scores["b"] = 2;
        scores["a"] += 10;
        Console.WriteLine(scores["a"] + scores["b"]);
        Console.WriteLine(scores.Count);
    }
}
"#,
    ),
    (
        "Agree5",
        r#"
using System;
class Grid
{
    private int[] cells = new int[4];
    public int this[int i]
    {
        get { return cells[i]; }
        set { cells[i] = value; }
    }
    public int Total
    {
        get
        {
            int sum = 0;
            foreach (int cell in cells) { sum += cell; }
            return sum;
        }
    }
    public int Doubled => Total * 2;
}
class Agree5
{
    static void Main()
    {
        Grid g = new Grid();
        g[0] = 3;
        g[3] = 4;
        g[0] += 1;
        Console.WriteLine(g[0] + " " + g[3]);
        Console.WriteLine(g.Total + " " + g.Doubled);
        try { throw new ArgumentException("bad"); }
        catch (InvalidOperationException e) { Console.WriteLine("wrong " + e.Message); }
        catch (ArgumentException e) { Console.WriteLine("right " + e.Message); }
    }
}
"#,
    ),
    (
        "Agree6",
        r#"
using System;
using System.Collections.Generic;
class Agree6
{
    static T Bigger<T>(T a, T b, bool second) { return second ? b : a; }
    static string Show<T>(List<T> items)
    {
        string text = "";
        foreach (T item in items) { text = text + item + ";"; }
        return text;
    }
    static void Main()
    {
        Console.WriteLine(Bigger(1, 2, true));
        Console.WriteLine(Bigger<string>("a", "b", false));
        List<int> numbers = new List<int>();
        numbers.Add(3);
        numbers.Add(5);
        Console.WriteLine(Show(numbers));
    }
}
"#,
    ),
    (
        "Agree13",
        r#"
using System;
class Agree13
{
    static void Grow(ref int value, int by) { value = value + by; }
    static bool Divide(int total, int by, out int result)
    {
        if (by == 0) { result = 0; return false; }
        result = total / by;
        return true;
    }
    static void Main()
    {
        int n = 1;
        for (int i = 0; i < 4; i++) { Grow(ref n, i); }
        Console.WriteLine(n);

        int answer;
        Console.WriteLine(Divide(9, 2, out answer) + " " + answer);
        Console.WriteLine(Divide(9, 0, out answer) + " " + answer);

        int[] values = { 1, 2, 3 };
        Grow(ref values[2], 10);
        Console.WriteLine(values[0] + " " + values[2]);
    }
}
"#,
    ),
    (
        "Agree12",
        r#"
using System;
record Item(string Name, int Count);
class Agree12
{
    static void Main()
    {
        Item a = new Item("nail", 3);
        Item b = new Item("nail", 3);
        Console.WriteLine(a);
        Console.WriteLine(a == b);
        Console.WriteLine(a == new Item("nail", 4));
        Console.WriteLine(a.Equals(b));
        Console.WriteLine(a.GetHashCode() == b.GetHashCode());
        Console.WriteLine(a.Name + a.Count);
    }
}
"#,
    ),
    (
        "Agree10",
        r#"
using System;
delegate int Op(int x);
delegate bool Test(int x);
class Agree10
{
    static int Apply(Op f, int v) { return f(v); }
    static int Count(int[] values, Test keep)
    {
        int total = 0;
        foreach (int value in values) { if (keep(value)) { total = total + 1; } }
        return total;
    }
    static void Main()
    {
        Console.WriteLine(Apply(x => x * x, 7));
        int[] numbers = { 1, 2, 3, 4, 5 };
        Console.WriteLine(Count(numbers, x => x % 2 == 0));
        Op chain = x => { int y = x + 1; return Apply(z => z * 3, y); };
        Console.WriteLine(chain(1));
    }
}
"#,
    ),
    (
        "Agree11",
        r#"
using System;
delegate int Op(int x);
delegate void Act();
class Agree11
{
    static Op Counter()
    {
        // Two lambdas over one captured variable, and the variable outlives
        // the method that declared it.
        int n = 0;
        Act bump = () => { n = n + 1; };
        bump();
        bump();
        bump();
        return x => x + n;
    }
    static void Main()
    {
        Console.WriteLine(Counter()(10));
        int factor = 2;
        Op scale = x => x * factor;
        Console.WriteLine(scale(5));
        factor = 7;
        Console.WriteLine(scale(5));
    }
}
"#,
    ),
    (
        "Agree7",
        r#"
using System;
delegate int Step(int x);
class Counter
{
    private int by;
    public Counter(int by) { this.by = by; }
    public int Add(int x) { return x + by; }
}
class Agree7
{
    static int Twice(Step s, int x) { return s(s(x)); }
    static int Half(int x) { return x / 2; }
    static void Main()
    {
        Console.WriteLine(Twice(Half, 40));
        Counter c = new Counter(5);
        Step add = c.Add;
        Console.WriteLine(Twice(add, 1));
        Step chain = new Step(Half);
        Console.WriteLine(chain(9) + " " + (chain == null));
    }
}
"#,
    ),
    (
        "Agree8",
        r#"
using System;
enum Colour { Red, Green = 4, Blue }
class Agree8
{
    static void Main()
    {
        // An enum prints as its name, which is what boxing one is for. A
        // value no member names prints as the number, as `Enum.ToString`
        // does.
        Colour c = Colour.Green;
        Console.WriteLine(c);
        Console.WriteLine(Colour.Blue);
        Console.WriteLine("is " + c);
        Console.WriteLine((int)c);
        Console.WriteLine(c == Colour.Green);
        Console.WriteLine((Colour)9);
        object boxed = c;
        Console.WriteLine(boxed is Colour);
    }
}
"#,
    ),
    (
        "Agree9",
        r#"
using System;
class Agree9
{
    // A `return` converts to the method's return type, which a backend
    // handed the wrong one would turn into invalid IL rather than a
    // diagnostic.
    static long Wide() { return 1; }
    static double Frac() { return 3; }
    static object Boxed() { return 5; }
    static double Arrow() => 7;
    static void Main()
    {
        Console.WriteLine(Wide());
        Console.WriteLine(Frac());
        Console.WriteLine(Boxed());
        Console.WriteLine(Arrow());
    }
}
"#,
    ),
];

/// The two backends read the same bound tree, so they have to agree.
///
/// This is the check that makes that true rather than hoped for: the same
/// program is interpreted and compiled, and the two outputs are compared with
/// each other rather than with something written down here.
#[test]
fn the_interpreter_and_the_compiler_agree() {
    for (name, source) in SHARED {
        let interpreted = rustlyn_interpret::run(source)
            .unwrap_or_else(|error| panic!("{name} did not interpret: {error}"));
        let assembly = build(name, source);
        let Some(compiled) = run(&assembly) else {
            println!("note: {name} was emitted but not run; no .NET host was found");
            continue;
        };
        assert_eq!(compiled, interpreted, "{name}: the two backends disagree");
    }
}

#[test]
fn an_unsupported_construct_is_reported_rather_than_mis_emitted() {
    // An `async` method whose return type names nothing the core library
    // here knows has no builder to drive its state machine, and saying so is
    // the whole point: the alternative is an assembly that is wrong in a way
    // nothing catches.
    let compilation = Compilation::create(vec![parse(SourceText::new(
        "Program.cs",
        "using System.Threading.Tasks;\n\
         class P {\n\
           static async Task<int> One() { await Task.Delay(1); return 1; }\n\
           static void Main() { }\n\
         }",
    ))]);
    let error = rustlyn_emit::emit(&compilation, "P").expect_err("this is not emitted");
    assert!(error.message.contains("builder"), "{}", error.message);
}

#[test]
fn an_iterator_hands_out_one_value_at_a_time() {
    check(
        "Iterating",
        r#"
using System;
using System.Collections.Generic;

class Program
{
    int seed = 10;

    IEnumerable<int> Shifted(int[] values)
    {
        // Nothing here runs until the first `MoveNext`, and the local lives
        // across every one of them.
        Console.WriteLine("walking");
        int total = 0;
        foreach (int value in values)
        {
            total = total + value;
            yield return total + seed;
        }
        yield return -1;
    }

    static IEnumerator<string> Two()
    {
        yield return "a";
        yield return "b";
        yield break;
    }

    static void Main()
    {
        Program program = new Program();
        int[] values = new int[] { 1, 2, 3 };
        IEnumerable<int> walk = program.Shifted(values);
        Console.WriteLine("made");
        foreach (int n in walk) { Console.WriteLine(n); }
        // An `IEnumerable` may be walked again, from the beginning.
        foreach (int n in walk) { Console.WriteLine(n); }

        IEnumerator<string> letters = Two();
        while (letters.MoveNext()) { Console.WriteLine(letters.Current); }
    }
}
"#,
        "made
walking
11
13
16
-1
walking
11
13
16
-1
a
b
",
    );
}

#[test]
fn a_record_struct_gets_the_members_the_language_promises() {
    check(
        "RecordStruct",
        r#"
using System;

readonly record struct Point(int X, int Y);

class RecordStruct
{
    static void Main()
    {
        Point one = new Point(3, 4);
        Point same = new Point(3, 4);
        Point other = new Point(3, 5);
        Console.WriteLine(one.X + one.Y);
        Console.WriteLine(one == same);
        Console.WriteLine(one != other);
        Console.WriteLine(one.ToString());
    }
}
"#,
        "7
True
True
Point { X = 3, Y = 4 }
",
    );
}

#[test]
fn nested_types() {
    check(
        "Nest",
        r#"
using System;
class Outer
{
    public int seed = 3;
    public class Inner
    {
        public int Doubled(int x) { return x + x; }
        // Nesting goes as deep as it is written; only the innermost name is
        // in the row, and a `NestedClass` row says where each one sits.
        public class Deeper { public string Say() { return "deep"; } }
    }
    private struct Point
    {
        public int X;
        public int Y;
        public int Sum() { return X + Y; }
    }
    public enum Colour { Red, Green }
    // The usual way to write a delegate, and the reason nested types matter.
    public delegate int Op(int x);

    public int Run()
    {
        Point p = new Point();
        p.X = seed;
        p.Y = 4;
        Op f = new Inner().Doubled;
        return f(p.Sum());
    }
    public static Colour Pick(bool green) { return green ? Colour.Green : Colour.Red; }
}
class Nest
{
    static void Main()
    {
        Console.WriteLine(new Outer().Run());
        Console.WriteLine(new Outer.Inner().Doubled(5));
        Console.WriteLine(new Outer.Inner.Deeper().Say());
        Console.WriteLine(Outer.Pick(true));
    }
}
"#,
        "14
10
deep
Green
",
    );
}

#[test]
fn a_compilation_with_no_entry_point_is_refused() {
    let compilation = Compilation::create(vec![parse(SourceText::new(
        "Program.cs",
        "class C { void M() { } }",
    ))]);
    let error = rustlyn_emit::emit(&compilation, "C").expect_err("there is no `Main`");
    assert!(error.message.contains("Main"), "{}", error.message);
}

#[test]
fn enum_operators() {
    check(
        "Flags",
        r"
using System;

[Flags]
enum Access { None = 0, Read = 1, Write = 2, Execute = 4 }

enum Level { Low = 1, High = 5 }

class Flags
{
    static void Main()
    {
        Access a = Access.Read | Access.Write;
        Console.WriteLine((a & Access.Write) != Access.None);
        Console.WriteLine((a & Access.Execute) == Access.None);
        Console.WriteLine((int)(a ^ Access.Read));
        Console.WriteLine((int)~Access.None);

        Level low = Level.Low;
        Level high = Level.High;
        Console.WriteLine(low < high);
        Console.WriteLine(high - low);
        Console.WriteLine(low + 4 == high);
    }
}
",
        "True\nTrue\n2\n-1\nTrue\n4\nTrue\n",
    );
}

#[test]
fn extension_methods() {
    check(
        "Extensions",
        r#"
using System;
using Helpers;

namespace Helpers
{
    static class StringExtensions
    {
        public static string Shout(this string text) { return text + "!"; }
        public static int Twice(this int value) { return value * 2; }
        public static T Echo<T>(this T value) { return value; }
        public static string Join(this string left, string right, string separator)
        {
            return left + separator + right;
        }
    }
}

class Extensions
{
    static void Main()
    {
        Console.WriteLine("hello".Shout());
        Console.WriteLine(21.Twice());
        Console.WriteLine("mirror".Echo());
        Console.WriteLine("a".Join("b", "-"));
        // An instance member wins over an extension with the same name.
        Console.WriteLine(StringExtensions.Twice(5));
    }
}
"#,
        "hello!\n42\nmirror\na-b\n10\n",
    );
}

#[test]
fn params_arrays_and_discards() {
    check(
        "Params",
        r#"
using System;
class Params
{
    static int Total(params int[] values)
    {
        int sum = 0;
        foreach (int v in values) { sum += v; }
        return sum;
    }
    static string Label(string prefix, params object[] parts)
    {
        string text = prefix;
        foreach (object p in parts) { text = text + ":" + p; }
        return text;
    }
    static void Main()
    {
        Console.WriteLine(Total());
        Console.WriteLine(Total(1, 2, 3));
        // Passing the array itself is the other form, and wins.
        Console.WriteLine(Total(new int[] { 4, 5 }));
        Console.WriteLine(Label("a"));
        Console.WriteLine(Label("a", 1, "b"));
        Func<int, int, int> both = (_, _) => 7;
        Console.WriteLine(both(1, 2));
        Console.WriteLine(nameof(Params));
        Console.WriteLine(nameof(Console.WriteLine));
    }
}
"#,
        "0\n6\n9\na\na:1:b\n7\nParams\nWriteLine\n",
    );
}

#[test]
fn local_functions() {
    check(
        "Local",
        r"
using System;
class Local
{
    private int offset = 10;

    int Shifted(int seed)
    {
        // Not static: it can reach `this`, which is what makes it an
        // instance method in metadata.
        int shift(int value) { return value + offset; }
        return shift(seed);
    }

    static int Run(int seed)
    {
        static int twice(int value) { return value * 2; }
        static int chain(int value)
        {
            static int plus(int a, int b) { return a + b; }
            return plus(twice(value), 1);
        }
        return chain(seed);
    }

    static void Main()
    {
        Console.WriteLine(Run(5));
        Console.WriteLine(new Local().Shifted(5));
    }
}
",
        "11\n15\n",
    );
}

#[test]
fn object_and_collection_initializers() {
    check(
        "Initializers2",
        r#"
using System;
using System.Collections.Generic;

class Point
{
    public int X;
    public int Y { get; set; }
    public string Name;
    public override string ToString() { return Name + " (" + X + ", " + Y + ")"; }
}

struct Pair
{
    public int A;
    public int B;
}

class Initializers
{
    static void Main()
    {
        Point p = new Point { X = 1, Y = 2, Name = "origin" };
        Console.WriteLine(p);
        // A value type has no reference to duplicate: it waits in a local.
        Pair q = new Pair { A = 3, B = 4 };
        Console.WriteLine(q.A + q.B);
        List<int> numbers = new List<int> { 5, 6, 7 };
        Console.WriteLine(numbers.Count);
        Console.WriteLine(numbers[2]);
        Console.WriteLine(new Point { X = 9 }.X);
    }
}
"#,
        "origin (1, 2)\n7\n3\n7\n9\n",
    );
}

#[test]
fn generic_constraints() {
    check(
        "Constraints",
        r"
using System;

interface IShape { double Area(); }

class Square : IShape
{
    public double Side;
    public double Area() { return Side * Side; }
}

class Constraints
{
    static double Total<T>(T[] shapes) where T : IShape
    {
        double sum = 0;
        foreach (T shape in shapes) { sum += shape.Area(); }
        return sum;
    }

    static string Describe<T>(T value) where T : IShape
    {
        // `object`'s members are there whatever the constraint says.
        return value.ToString() + ' ' + value.Area();
    }

    static void Main()
    {
        Square[] squares = new Square[] { new Square { Side = 2 }, new Square { Side = 3 } };
        Console.WriteLine(Total<Square>(squares));
        Console.WriteLine(Describe<Square>(squares[0]));
    }
}
",
        "13\nSquare 4\n",
    );
}

#[test]
fn static_members_of_a_constructed_type() {
    check(
        "StaticGeneric",
        r#"
using System;

class Holder<T>
{
    public static T Value;
    public static int Count;
    public static T Echo(T value) { Count = Count + 1; return value; }
    public static string Describe() { return "holder of " + Count; }
}

class StaticGeneric
{
    static void Main()
    {
        Holder<int>.Value = 7;
        Holder<string>.Value = "seven";
        // Each construction has storage of its own: that is what makes
        // `Holder<int>.Count` and `Holder<string>.Count` two fields.
        Console.WriteLine(Holder<int>.Echo(Holder<int>.Value));
        Console.WriteLine(Holder<string>.Echo(Holder<string>.Value));
        Console.WriteLine(Holder<int>.Echo(1));
        Console.WriteLine(Holder<int>.Count);
        Console.WriteLine(Holder<string>.Count);
        Console.WriteLine(Holder<int>.Describe());
    }
}
"#,
        "7\nseven\n1\n2\n1\nholder of 2\n",
    );
}

#[test]
fn null_conditional_access() {
    check(
        "Conditional2",
        r#"
using System;

class Node
{
    public int Value;
    public string Text;
    public Node Next;
    public int Twice() { return Value * 2; }
    public void Shout() { Console.WriteLine(Text + "!"); }
}

class Conditional
{
    static void Main()
    {
        Node head = new Node { Value = 21, Text = "hi" };
        Node none = null;

        Console.WriteLine(head?.Value);
        Console.WriteLine(head?.Twice());
        Console.WriteLine(head?.Text);
        Console.WriteLine(none?.Text == null);
        head?.Shout();
        none?.Shout();

        // The receiver is evaluated once, and the chain stops at the first
        // null rather than throwing.
        head.Next = new Node { Value = 3, Text = "tail" };
        Console.WriteLine(head?.Next?.Text);
        Console.WriteLine(head?.Next?.Next?.Text == null);
    }
}
"#,
        "21\n42\nhi\nTrue\nhi!\ntail\nTrue\n",
    );
}

#[test]
fn a_partial_generic_type_has_one_set_of_parameters() {
    check(
        "Partial",
        r#"
using System;

interface INamed { string Name(); }

partial class Pair<T> where T : INamed
{
    public T First;
}

partial class Pair<T>
{
    public T Second;
    public string Both() { return First.Name() + '+' + Second.Name(); }
}

class Person : INamed
{
    public string Who;
    public string Name() { return Who; }
}

class Partial
{
    static void Main()
    {
        Pair<Person> pair = new Pair<Person>
        {
            First = new Person { Who = "a" },
            Second = new Person { Who = "b" },
        };
        Console.WriteLine(pair.Both());
    }
}
"#,
        "a+b\n",
    );
}

#[test]
fn deconstruction_declarations() {
    check(
        "Deconstruct",
        r#"
using System;

class Point
{
    public int X;
    public int Y;
    public void Deconstruct(out int x, out int y) { x = X; y = Y; }
}

record Pair(string Left, string Right);

class Deconstruct
{
    static void Main()
    {
        Point p = new Point { X = 3, Y = 4 };
        var (x, y) = p;
        Console.WriteLine(x + y);
        (int a, int b) = p;
        Console.WriteLine(a * b);
        // A record's `Deconstruct` is the language's own, and works the same.
        var (left, right) = new Pair("l", "r");
        Console.WriteLine(left + right);
    }
}
"#,
        "7\n12\nlr\n",
    );
}

#[test]
fn named_arguments() {
    check(
        "Named",
        r#"
using System;

class Report
{
    public string Title;
    public int Count;
    public Report(string title, int count) { Title = title; Count = count; }
    public override string ToString() { return Title + ":" + Count; }
}

class Named
{
    static int Subtract(int left, int right) { return left - right; }

    static void Main()
    {
        Console.WriteLine(Subtract(left: 10, right: 1));
        // The names decide, not the order they were written in.
        Console.WriteLine(Subtract(right: 1, left: 10));
        static string join(string prefix, string suffix) { return prefix + suffix; }
        Console.WriteLine(join(suffix: "b", prefix: "a"));
        Console.WriteLine(new Report(count: 2, title: "t"));
    }
}
"#,
        "9\n9\nab\nt:2\n",
    );
}

#[test]
fn a_lambda_named_ahead_of_arguments_stored_first() {
    check(
        "NamedLambda",
        r#"
using System;

class Point
{
    public int X;
    public Point(int x) { X = x; }
}

class NamedLambda
{
    static int Get(int value)
    {
        Console.WriteLine("get " + value);
        return value;
    }

    static void Apply(Func<int, int> f, int a, int b) { Console.WriteLine(f(a) + b); }
    static void Show(Point at, int a) { Console.WriteLine(at.X + a); }
    static void Each(Action<string> action, string text) { action(text); }

    static void Main()
    {
        // The parameter the lambda goes to comes first, and what was written
        // before it is worked out, in that order, before the call.
        Apply(b: Get(1), a: Get(2), f: x => x * 10);
        // So with a `new()` the parameter's type makes.
        Show(a: Get(3), at: new(4));
        // And with a method group.
        Each(text: Get(5).ToString(), action: Console.WriteLine);
    }
}
"#,
        "get 1\nget 2\n21\nget 3\n7\nget 5\n5\n",
    );
}

#[test]
fn user_defined_conversions() {
    check(
        "Conversions",
        r#"
using System;

struct Meters
{
    public int Value;
    public static implicit operator Meters(int value)
    {
        Meters m = new Meters();
        m.Value = value;
        return m;
    }
    public static implicit operator int(Meters m) { return m.Value; }
}

class Conversions
{
    static string Describe(Meters m) { return "m" + m.Value; }

    static void Main()
    {
        // The argument is an `int` and the parameter is not: the type said
        // how values reach it, and that code runs.
        Console.WriteLine(Describe(7));
        Meters five = 5;
        Console.WriteLine(five.Value);
        int back = five;
        Console.WriteLine(back);
    }
}
"#,
        "m7\n5\n5\n",
    );
}

#[test]
fn overloads_are_collected_across_the_hierarchy() {
    check(
        "Overloads",
        r#"
using System;

class Visitor
{
    public virtual string Visit(int value) { return "int " + value; }
    public virtual string Visit(string text) { return "string " + text; }
    public virtual string Visit(bool flag) { return "bool " + flag; }
}

class Louder : Visitor
{
    // Overriding one overload does not hide the other two.
    public override string Visit(int value) { return "INT " + value; }
}

class Overloads
{
    static void Main()
    {
        Visitor v = new Louder();
        Console.WriteLine(v.Visit(1));
        Console.WriteLine(v.Visit("a"));
        Console.WriteLine(new Louder().Visit(true));
        Console.WriteLine(new Louder().Visit("b"));
        // `out _` throws the value away and still gives the callee somewhere
        // to put it.
        Console.WriteLine(int.TryParse("7", out _));
    }
}
"#,
        "INT 1\nstring a\nbool True\nstring b\nTrue\n",
    );
}

#[test]
fn a_member_inherited_from_a_construction() {
    check(
        "Inherited",
        r#"
using System;

class Visitor<TArgument, TResult>
{
    public virtual TResult Visit(string node, TArgument argument)
    {
        return Default(node, argument);
    }
    public virtual TResult Default(string node, TArgument argument)
    {
        throw new InvalidOperationException("no");
    }
}

class Counter : Visitor<int, string>
{
    // The base is a construction, so `argument` is an `int` here and
    // `Visit` gives back a `string`.
    public override string Default(string node, int argument)
    {
        return node + argument;
    }
    public string Run() { return Visit("n", 7); }
}

class Inherited
{
    static void Main()
    {
        Console.WriteLine(new Counter().Run());
    }
}
"#,
        "n7\n",
    );
}

#[test]
fn foreach_over_deconstructed_values() {
    check(
        "ForEachPairs",
        r#"
using System;
using System.Collections.Generic;

class Pair
{
    private int x;
    private int y;
    public Pair(int x, int y) { this.x = x; this.y = y; }
    public void Deconstruct(out int a, out int b) { a = x; b = y; }
}

class ForEachPairs
{
    static void Main()
    {
        List<Pair> pairs = new List<Pair> { new Pair(1, 2), new Pair(3, 4) };
        // The loop variable is one nobody named, taken apart on each turn.
        foreach (var (a, b) in pairs)
        {
            Console.WriteLine(a + b);
        }
    }
}
"#,
        "3\n7\n",
    );
}

#[test]
fn ref_locals() {
    check(
        "RefLocals",
        r#"
using System;

struct Counter { public int Hits; }

class RefLocals
{
    static void Bump(ref int slot) { slot = slot + 1; }

    static void Main()
    {
        int[] numbers = new int[] { 1, 2, 3 };
        // A name for a place, not a copy of what is in it.
        ref int first = ref numbers[0];
        first = 10;
        ref var last = ref numbers[2];
        last = last + 30;
        Console.WriteLine(numbers[0] + " " + numbers[2] + " " + first);

        Counter[] counters = new Counter[] { new Counter() };
        ref Counter only = ref counters[0];
        only.Hits = 4;
        Bump(ref only.Hits);
        Console.WriteLine(counters[0].Hits);
    }
}
"#,
        "10 33 10\n5\n",
    );
}

#[test]
fn a_derived_overload_wins_once_both_apply() {
    check(
        "Derived",
        r#"
using System;
using static Helpers.Numbers;

namespace Helpers
{
    static class Numbers
    {
        public const int Two = 2;
        public static int Triple(int value) { return value * 3; }
    }
}

struct Wide
{
    public int Value;
    public static implicit operator Wide(int value)
    {
        Wide w = new Wide();
        w.Value = value;
        return w;
    }
}

class Narrow
{
    public string Take(int value) { return "int " + value; }
}

class Wider : Narrow
{
    // Reachable from an `int` only through the conversion, and still the one
    // a call from here picks: a type's own beats what its base declares.
    public string Take(Wide value) { return "wide " + value.Value; }
    public string Describe(string format) { return "formatted " + format; }
}

class Derived
{
    static void Main()
    {
        Console.WriteLine(new Wider().Take(1));
        Console.WriteLine(((Narrow)new Wider()).Take(1));
        // Declaring `Describe(string)` does not hide `object.ToString()`.
        Console.WriteLine(new Wider().ToString());
        Console.WriteLine(Triple(Two));
    }
}
"#,
        "wide 1\nint 1\nWider\n6\n",
    );
}

#[test]
fn a_deconstruction_discards_and_assigns() {
    check(
        "Apart",
        r#"
using System;

class Pair
{
    public int First;
    public string Second;
    public int Third;

    public void Deconstruct(out int first, out string second, out int third)
    {
        first = First;
        second = Second;
        third = Third;
    }
}

class Apart
{
    static void Main()
    {
        Pair pair = new Pair();
        pair.First = 1;
        pair.Second = "two";
        pair.Third = 3;

        // `_` still gets a slot to be written into; nobody can read it back.
        var (a, _, c) = pair;
        Console.WriteLine(a + " " + c);

        // A target may mix a declaration with somewhere that already exists.
        int existing = 0;
        (var first, string second, existing) = pair;
        Console.WriteLine(first + " " + second + " " + existing);
    }
}
"#,
        "1 3\n1 two 3\n",
    );
}

#[test]
fn a_using_inside_a_namespace_resolves_against_it() {
    check(
        "Scoped",
        r#"
namespace App
{
    // The target is `App.Kind`, which is only a name here because the
    // directive sits inside the namespace that declares it.
    using static Kind;
    using System;

    class Shapes
    {
        public class Inner { public int Value; }
    }

    // Nothing of its own: `Derived.Inner` is what its base declares.
    class Derived : Shapes { }

    class Scoped
    {
        static string Name(Kind kind)
        {
            switch (kind)
            {
                case Equal: return "equal";
                case Less: return "less";
            }
            return "?";
        }

        static void Main()
        {
            Console.WriteLine(Name(Less));
            Derived.Inner inner = new Derived.Inner();
            inner.Value = 7;
            Console.WriteLine(inner.Value);
        }
    }
}

namespace App
{
    enum Kind { Equal, Less }
}
"#,
        "less\n7\n",
    );
}

/// `[ModuleInitializer]` methods run from `<Module>..cctor`, in lexical
/// order, before `Main` — whatever `[Conditional]` says about the attribute.
#[test]
fn module_initializers_run_before_main() {
    check(
        "ModuleInitializers",
        r#"
using System;
using System.Runtime.CompilerServices;

class C
{
    [ModuleInitializer]
    internal static void Second() => Console.Write("2");

    [ModuleInitializer]
    internal static void Third() => Console.Write("3");
}

class Program
{
    [ModuleInitializer]
    internal static void First() => Console.Write("1");

    static void Main() => Console.WriteLine("M");
}

namespace System.Runtime.CompilerServices
{
    [System.Diagnostics.Conditional("NOWHERE")]
    class ModuleInitializerAttribute : Attribute { }
}
"#,
        "231M\n",
    );
}

/// Only a `Main` Roslyn would start at is an entry point: not a generic one,
/// not one in a generic type, not one returning something else, and an
/// `async` one only where there is no synchronous one (which needs `Task`,
/// and so the benchmark, to check).
#[test]
fn the_entry_point_is_the_one_main_that_qualifies() {
    check(
        "EntryPointRules",
        r#"
using System;

static class C
{
    static void Main<T>() { Console.WriteLine(1); }

    static class CC<T>
    {
        static void Main() { Console.WriteLine(2); }
    }

    static float Main(int x) => 0;
}

static class D<T>
{
    static class DD
    {
        static void Main() { Console.WriteLine(4); }
    }
}

static class E
{
    static void Main() { Console.WriteLine(5); }

}
"#,
        "5\n",
    );
}

#[test]
fn a_name_may_skip_an_optional_parameter() {
    check(
        "Skipped",
        r#"
using System;

class Skipped
{
    static string Describe(string what, int times = 2, string suffix = "!")
    {
        string all = "";
        for (int i = 0; i < times; i++) { all = all + what; }
        return all + suffix;
    }

    // Two overloads whose last parameter shares a name: only one of them can
    // take four arguments without a hole, and that is the one meant.
    static string Pick(int a, int b, bool flag) { return "three " + flag; }
    static string Pick(int a, int b, string middle, bool flag) { return "four " + middle; }

    static void Main()
    {
        // `times` is skipped over and takes the 2 written on the declaration.
        Console.WriteLine(Describe("ab", suffix: "?"));
        Console.WriteLine(Describe("c", 3));
        Console.WriteLine(Pick(1, 2, flag: true));
    }
}
"#,
        "abab?\nccc!\nthree True\n",
    );
}

#[test]
fn a_type_nested_in_a_generic_one_spells_its_parameters() {
    check(
        "NestedInGeneric",
        r#"
using System;

class Holder<T>
{
    private T _value;

    public Holder(T value) { _value = value; }

    // Written bare, and it means `Holder<T>.Walker`: the parameter comes
    // from the type around it rather than from anything written here.
    public Walker Read() { return new Walker(this); }

    public struct Walker
    {
        private Holder<T> _holder;

        public Walker(Holder<T> holder) { _holder = holder; }

        public T Current { get { return _holder._value; } }
    }
}

class Nested
{
    static void Main()
    {
        Holder<string> words = new Holder<string>("here");
        // `Current` is a `string` because the construction says so, and it is
        // the same `T` on both sides of the nesting.
        string read = words.Read().Current;
        Console.WriteLine(read);

        Holder<int>.Walker counter = new Holder<int>(7).Read();
        int number = counter.Current;
        Console.WriteLine(number);
    }
}
"#,
        "here\n7\n",
    );
}

#[test]
fn a_struct_is_called_through_its_address() {
    check(
        "Address",
        r#"
using System;

struct Counter
{
    private int _count;

    public Counter(int count) { _count = count; }

    public int Count { get { return _count; } }

    public int Next() { return _count + 1; }

    public override string ToString() { return "counter " + _count; }
}

class Address
{
    static Counter Make() { return new Counter(7); }

    static void Main()
    {
        // The receiver is a value with nowhere of its own to live, so it gets
        // a slot to be addressed in; `callvirt` on that address is not IL a
        // runtime will accept.
        Console.WriteLine(Make().Count);
        Console.WriteLine(Make().Next());
        Console.WriteLine(Make().ToString());

        Counter held = new Counter(1);
        Console.WriteLine(held.Count);
    }
}
"#,
        "7\n8\ncounter 7\n1\n",
    );
}

#[test]
fn an_inherited_member_is_read_through_the_construction() {
    check(
        "Inherited2",
        r#"
using System;

class Adapter
{
    public string Name;
    public Adapter(string name) { Name = name; }
}

abstract class Manager<TSymbol>
{
    // Nested in a generic type, and reached through a base that fixed its
    // arguments: `Underlying` is an `Adapter` wherever `Embedded` reads it.
    public abstract class Common
    {
        public readonly TSymbol Underlying;
        protected Common(TSymbol underlying) { Underlying = underlying; }
    }
}

sealed class Manager : Manager<Adapter>
{
}

sealed class Embedded : Manager.Common
{
    public Embedded(Adapter underlying) : base(underlying) { }

    // With no receiver written, and with one.
    public string Bare() { return Underlying.Name; }
    public string Written() { return this.Underlying.Name; }
}

class Inherited
{
    static void Main()
    {
        Embedded embedded = new Embedded(new Adapter("held"));
        Console.WriteLine(embedded.Bare());
        Console.WriteLine(embedded.Written());
    }
}
"#,
        "held\nheld\n",
    );
}

#[test]
fn a_local_function_is_a_name_before_it_is_declared() {
    check(
        "Ahead",
        r#"
using System;

class Ahead
{
    static void Main()
    {
        // Handed to something else well above where it is written: a local
        // function is in scope for the whole block, not from its declaration
        // onwards.
        Console.WriteLine(Apply(twice, 4));
        Console.WriteLine(Apply(x => x + 1, 4));

        static int twice(int value) { return value * 2; }
    }

    static int Apply(Func<int, int> what, int to) { return what(to); }
}
"#,
        "8\n5\n",
    );
}

#[test]
fn an_enum_member_is_a_constant_of_the_underlying_type() {
    check(
        "Widths",
        r#"
using System;

[Flags]
enum Wide : uint
{
    None = 0,
    Low = 1u << 3,
    // No `int` holds this one, and Roslyn's own `BinderFlags` has it.
    Top = 1u << 31,
}

enum Long : long
{
    Big = 5000000000L,
}

enum Small : byte
{
    One = 1,
    Two,
}

class Widths
{
    static void Main()
    {
        Console.WriteLine((uint)Wide.Top);
        Console.WriteLine((uint)Wide.Low);
        Console.WriteLine((long)Long.Big);
        Console.WriteLine((byte)Small.Two);
    }
}
"#,
        "2147483648\n8\n5000000000\n2\n",
    );
}

#[test]
fn a_throw_can_stand_where_a_value_was_wanted() {
    check(
        "Thrown",
        r#"
using System;

class Thrown
{
    static string Require(string value)
    {
        // Throwing instead of producing one fits wherever a value was
        // wanted, and has no type of its own.
        return value ?? throw new Exception("nothing given");
    }

    static void Again()
    {
        try
        {
            throw new Exception("first");
        }
        catch (Exception)
        {
            // A bare `throw;` keeps the stack trace the exception already
            // had, which `throw e;` would throw away.
            throw;
        }
    }

    static void Main()
    {
        Console.WriteLine(Require("here"));
        try { Require(null); } catch (Exception e) { Console.WriteLine(e.Message); }
        try { Again(); } catch (Exception e) { Console.WriteLine(e.Message); }

        // `checked` and `unchecked` say how arithmetic overflows, and `x!`
        // says something to an analysis there is none of.
        int wide = unchecked(1 + 2);
        int narrow = checked(3 + 4);
        string held = "kept";
        Console.WriteLine(wide + " " + narrow + " " + held!.Length);
    }
}
"#,
        "here\nnothing given\nfirst\n3 7 4\n",
    );
}

#[test]
fn goto_case_jumps_to_another_section() {
    check(
        "Jumped",
        r#"
using System;

class Jumped
{
    static string Describe(int value)
    {
        string all = "";
        switch (value)
        {
            case 1:
                all = all + "one ";
                // Carries on from the section that handles 2, rather than
                // falling out of the switch.
                goto case 2;
            case 2:
                all = all + "two ";
                goto default;
            case 3:
                all = all + "three ";
                break;
            default:
                all = all + "rest";
                break;
        }
        return all;
    }

    static void Main()
    {
        Console.WriteLine(Describe(1));
        Console.WriteLine(Describe(2));
        Console.WriteLine(Describe(3));
        Console.WriteLine(Describe(9));
    }
}
"#,
        "one two rest\ntwo rest\nthree \nrest\n",
    );
}

#[test]
fn a_recursive_pattern_reads_members_and_takes_a_value_apart() {
    check(
        "Shapes",
        r#"
using System;

class Box
{
    public int Width;
    public Box Inner;

    public void Deconstruct(out int width, out Box inner)
    {
        width = Width;
        inner = Inner;
    }
}

class Shapes
{
    static string Describe(object value)
    {
        // A type test, then a member read, then another pattern on what it
        // gave back.
        if (value is Box { Width: > 2, Inner: { Width: var inner } })
        {
            return "nested " + inner;
        }
        // Taken apart by `Deconstruct`, with a name for the whole.
        if (value is Box (1, null) held)
        {
            return "one " + held.Width;
        }
        if (value is Box { Width: 5 })
        {
            return "five";
        }
        return "none";
    }

    static void Main()
    {
        Box deep = new Box();
        deep.Width = 3;
        deep.Inner = new Box();
        deep.Inner.Width = 7;
        Console.WriteLine(Describe(deep));

        Box one = new Box();
        one.Width = 1;
        Console.WriteLine(Describe(one));

        Box five = new Box();
        five.Width = 5;
        Console.WriteLine(Describe(five));

        Console.WriteLine(Describe("something else"));
    }
}
"#,
        "nested 7\none 1\nfive\nnone\n",
    );
}

#[test]
fn a_property_pattern_reaches_through_a_chain() {
    check(
        "Reached",
        r#"
using System;

class Node
{
    public Node Parent;
    public int Width;
}

class Reached
{
    static string Describe(Node node)
    {
        // `{ Parent.Width: 1 }` is `{ Parent: { Width: 1 } }` written
        // shorter, and means exactly that.
        if (node is { Parent.Width: 1 }) { return "parent one"; }
        if (node is { Parent.Parent.Width: 2 }) { return "grandparent two"; }
        return "none";
    }

    static void Main()
    {
        Node one = new Node();
        one.Parent = new Node();
        one.Parent.Width = 1;
        Console.WriteLine(Describe(one));

        Node two = new Node();
        two.Parent = new Node();
        two.Parent.Parent = new Node();
        two.Parent.Parent.Width = 2;
        Console.WriteLine(Describe(two));

        Console.WriteLine(Describe(new Node()));
    }
}
"#,
        "parent one\ngrandparent two\nnone\n",
    );
}

#[test]
fn a_static_member_of_a_generic_type_knows_its_construction() {
    check(
        "StaticGeneric2",
        r#"
using System;

struct Holder<T>
{
    public T Value;

    // Declared on `Holder<T>`, reached as `Holder<int>` and `Holder<string>`:
    // two members of two constructions, one definition.
    public static Holder<T> Of(T value) { Holder<T> h = new Holder<T>(); h.Value = value; return h; }

    public static implicit operator T(Holder<T> holder) { return holder.Value; }

    public static string Describe() { return "holder"; }
}

class StaticGeneric
{
    static void Main()
    {
        // The receiver is a type, and it says which construction.
        Console.WriteLine(Holder<int>.Of(7).Value);
        Console.WriteLine(Holder<string>.Of("x").Value);

        // The operator's call has no receiver at all: what it takes and what
        // it gives back are all there is to say `T` is `int`.
        int n = Holder<int>.Of(41);
        string s = Holder<string>.Of("y");
        Console.WriteLine(n + 1);
        Console.WriteLine(s);
        Console.WriteLine(Holder<int>.Describe());
    }
}
"#,
        "7\nx\n42\ny\nholder\n",
    );
}

#[test]
fn a_nested_type_sees_what_the_type_around_it_declares() {
    check(
        "Nested",
        r#"
using System;

class Base { public int Inherited() { return 1; } }

static class Outer
{
    private const int Limit = 5;
    private static int Shared = 6;
    private static string Encode(string s) { return s + "!"; }

    private sealed class Inner : Base
    {
        // Every one of these belongs to the type this one is nested in, and
        // is written with nothing in front of it.
        public string Go() { return Encode("a") + Limit + Shared + Inherited(); }
    }

    // A sibling nested type named from inside another keeps its arguments:
    // `Holder<int>` is a construction, not the bare definition.
    private sealed class Holder<T>
    {
        public static string Name() { return "holder"; }
    }

    private sealed class Uses
    {
        public string Go() { return Holder<int>.Name() + Holder<string>.Name(); }
    }

    public static void Run()
    {
        Console.WriteLine(new Inner().Go());
        Console.WriteLine(new Uses().Go());
    }
}

class Nested { static void Main() { Outer.Run(); } }
"#,
        "a!561\nholderholder\n",
    );
}

#[test]
fn a_constant_meets_an_unsigned_operand() {
    check(
        "Unsigned",
        r"
using System;

class Unsigned
{
    static uint Align(uint position, uint alignment)
    {
        // `alignment - 1` is a `uint`: the `1` is a constant that reaches
        // `uint`, so the operator is the unsigned one and the result fits
        // back into a `uint` without a cast.
        uint result = position & ~(alignment - 1);
        if (result == position) { return result; }
        return result + alignment;
    }

    static void Main()
    {
        Console.WriteLine(Align(13, 8));
        Console.WriteLine(Align(16, 8));
        ulong big = 1UL << 40;
        Console.WriteLine(big + 1);
        Console.WriteLine(big - 1);
    }
}
",
        "16\n16\n1099511627777\n1099511627775\n",
    );
}

#[test]
fn a_ref_local_points_at_where_the_value_lives() {
    check(
        "RefLocal",
        r"
using System;

struct Counter { public int Hits; }

class RefLocal
{
    static ref int Slot(int[] cells, int at) { return ref cells[at]; }

    static void Main()
    {
        int[] cells = new int[3];
        // A `ref` local holds where the element is, so writing through it
        // writes the array.
        ref int here = ref cells[1];
        here = 7;
        here += 2;
        Console.WriteLine(cells[1]);

        // And the same through a method that returns one.
        ref int there = ref Slot(cells, 2);
        there = 5;
        Console.WriteLine(cells[2]);

        Counter counter = new Counter();
        ref int hits = ref counter.Hits;
        hits = 4;
        Console.WriteLine(counter.Hits);
    }
}
",
        "9\n5\n4\n",
    );
}

#[test]
fn a_struct_chains_to_the_constructor_nobody_wrote() {
    check(
        "StructThis",
        r#"
using System;

struct Pair
{
    public int X;
    public int Y;

    // `: this()` names the parameterless constructor every struct has and
    // nobody writes: the fields start at zero.
    public Pair(int x) : this() { X = x; }
    public Pair(int x, int y) : this(x) { Y = y; }
}

class StructThis
{
    static void Main()
    {
        Pair one = new Pair(3);
        Console.WriteLine(one.X + " " + one.Y);
        Pair two = new Pair(3, 4);
        Console.WriteLine(two.X + " " + two.Y);
    }
}
"#,
        "3 0\n3 4\n",
    );
}

#[test]
fn a_value_that_is_not_a_variable_gets_somewhere_to_live() {
    check(
        "Spill",
        r"
using System;

struct Counter
{
    public int Hits;
    public int Doubled() { return Hits * 2; }
}

class Spill
{
    static Counter Make(int hits) { Counter c = new Counter(); c.Hits = hits; return c; }

    static void Main()
    {
        bool flag = true;
        Counter a = Make(3);
        Counter b = Make(4);
        // A struct's method takes the address of its receiver, and neither of
        // these receivers is a variable: each needs somewhere to live first.
        Console.WriteLine((flag ? a : b).Doubled());
        Console.WriteLine(Make(5).Doubled());
    }
}
",
        "6\n10\n",
    );
}

#[test]
fn a_field_of_an_array_element_is_written_in_place() {
    check(
        "ElementField",
        r"
using System;

struct Entry { public int Width; public int Height; }

class ElementField
{
    static void Main()
    {
        Entry[] entries = new Entry[2];
        for (int i = 0; i < entries.Length; i++)
        {
            // The element's address is where this writes: a copy would be
            // thrown away and the array would stay at zero.
            entries[i].Width = i + 1;
            entries[i].Height = (i + 1) * 10;
        }
        Console.WriteLine(entries[0].Width + entries[0].Height);
        Console.WriteLine(entries[1].Width + entries[1].Height);

        // And one nested a level deeper.
        Holder holder = new Holder();
        holder.First.Width = 7;
        Console.WriteLine(holder.First.Width);
    }
}

struct Holder { public Entry First; }
",
        "11\n22\n7\n",
    );
}

#[test]
fn what_has_no_type_until_something_says() {
    check(
        "TargetTyped",
        r#"
using System;

class Box
{
    public int Value;
    public Box(int value) { Value = value; }
    public Box() { Value = -1; }
}

class TargetTyped
{
    static int Sum(int a, long b) { return a + (int)b; }
    static string Name(string s) { return s; }

    static void Main()
    {
        // `default` is whatever it is being given to, and nothing else.
        Console.WriteLine(Sum(default, default));
        int n = default;
        Console.WriteLine(n);
        Console.WriteLine(Name(default) == null);

        // `new(...)` says everything but what is being made.
        Box one = new(7);
        Box two = new();
        Console.WriteLine(one.Value + two.Value);

        // `a ?? throw ...` is an `a`: a `throw` produces nothing to be.
        string given = "x";
        string kept = given ?? throw new ArgumentNullException(nameof(given));
        Console.WriteLine(kept);
    }
}
"#,
        "0\n0\nTrue\n6\nx\n",
    );
}

#[test]
fn goto_jumps_to_a_label() {
    check(
        "Goto",
        r#"
using System;

class Goto
{
    static int Count(int n)
    {
        int total = 0;
        int i = 0;
    Again:
        if (i >= n) { goto Done; }
        total += i;
        i++;
        goto Again;
    Done:
        return total;
    }

    static string Leave(bool fail)
    {
        try
        {
            // Jumping out of a `try` is a `leave`, not a branch.
            if (fail) { goto Handled; }
            return "kept";
        }
        finally { Console.WriteLine("finally"); }
    Handled:
        return "left";
    }

    static void Main()
    {
        Console.WriteLine(Count(4));
        Console.WriteLine(Leave(false));
        Console.WriteLine(Leave(true));
    }
}
"#,
        "6\nfinally\nkept\nfinally\nleft\n",
    );
}

#[test]
fn a_value_is_boxed_before_it_is_asked_what_it_is() {
    check(
        "BoxedTest",
        r#"
using System;

interface IShape { int Sides(); }
struct Square : IShape { public int Sides() { return 4; } }
struct Round { }

class BoxedTest
{
    // An unconstrained `T` may be a value or a reference, and `isinst` asks
    // about a reference: the box is what the runtime compares against.
    static string Describe<T>(T value)
    {
        if (value is IShape shape) { return "shape " + shape.Sides(); }
        if (value is string text) { return "text " + text; }
        return "other";
    }

    static void Main()
    {
        Console.WriteLine(Describe(new Square()));
        Console.WriteLine(Describe("x"));
        Console.WriteLine(Describe(new Round()));
        Square square = new Square();
        Console.WriteLine(square is IShape);
    }
}
"#,
        "shape 4\ntext x\nother\nTrue\n",
    );
}

#[test]
fn a_ref_indexer_is_written_through() {
    check(
        "RefIndexer",
        r"
using System;

struct Row
{
    private int[] _cells;
    public Row(int size) { _cells = new int[size]; }
    // No setter, and none needed: the getter hands back where the value is.
    public ref int this[int at] { get { return ref _cells[at]; } }
    public int Count { get { return _cells.Length; } }
}

class RefIndexer
{
    static void Main()
    {
        Row row = new Row(3);
        row[0] = 7;
        row[1] = row[0] + 1;
        row[2]++;
        Console.WriteLine(row[0] + row[1] + row[2]);
        Console.WriteLine(row.Count);
    }
}
",
        "16\n3\n",
    );
}

#[test]
fn an_explicit_implementation_is_reachable_only_through_the_interface() {
    check(
        "Explicit",
        r#"
using System;

interface ICounter
{
    int Count { get; }
    void Step();
}

class Both : ICounter
{
    private int _count;
    // The type's own `Count` and the interface's are two members, and the
    // explicit one is reachable only through `ICounter`.
    public string Count { get { return "mine"; } }
    int ICounter.Count { get { return _count; } }
    void ICounter.Step() { _count = _count + 2; }
}

class Explicit
{
    static void Main()
    {
        Both both = new Both();
        ICounter counter = both;
        counter.Step();
        counter.Step();
        Console.WriteLine(both.Count);
        Console.WriteLine(counter.Count);
    }
}
"#,
        "mine\n4\n",
    );
}

#[test]
fn a_nested_type_of_a_base_is_named_with_the_bases_arguments() {
    check(
        "BaseNested",
        r#"
using System;

class Pass<TState>
{
    // Written in terms of the enclosing type's parameter, which every type
    // nested here carries as one of its own.
    public interface IState { TState Step(); }

    public TState Run(TState start)
    {
        IState state = (IState)start;
        return state.Step();
    }
}

// `IState` written below means `Pass<Counter>.IState`: the argument comes
// from the base the name was found through, and nothing in the name says so.
class Counting : Pass<Counting.Counter>
{
    public class Counter : IState
    {
        public int Value;
        public Counter Step() { return new Counter { Value = Value + 1 }; }
    }
}

class BaseNested
{
    static void Main()
    {
        Counting counting = new Counting();
        Counting.Counter one = new Counting.Counter();
        one.Value = 41;
        Console.WriteLine(counting.Run(one).Value);
    }
}
"#,
        "42\n",
    );
}

#[test]
fn an_abstract_override_stays_in_the_slot_it_answers_for() {
    check(
        "AbstractOverride",
        r#"
using System;

abstract class Node
{
    public abstract string Name { get; }
    public abstract string Describe();
}

abstract class Middle : Node
{
    // Says the slot `Node` opened has to be answered again, rather than
    // opening a second one that nothing would ever fill.
    public abstract override string Name { get; }
    public abstract override string Describe();
}

class Leaf : Middle
{
    public override string Name { get { return "leaf"; } }
    public override string Describe() { return "a " + Name; }
}

class AbstractOverride
{
    static void Main()
    {
        Node node = new Leaf();
        Console.WriteLine(node.Name);
        Console.WriteLine(node.Describe());
    }
}
"#,
        "leaf\na leaf\n",
    );
}

#[test]
fn a_get_only_property_is_set_through_its_field_in_the_constructor() {
    check(
        "GetOnly",
        r#"
using System;

class Window
{
    // No setter, and none meant: the constructor writes the field the
    // property reads, which is what C# means by assigning to it here.
    public string Text { get; }
    public int Position { get; private set; }

    public Window(string text)
    {
        Text = text;
        Position = text.Length;
    }

    public void Step() { Position = Position - 1; }
}

class GetOnly
{
    static void Main()
    {
        Window window = new Window("hello");
        Console.WriteLine(window.Text);
        Console.WriteLine(window.Position);
        window.Step();
        Console.WriteLine(window.Position);
    }
}
"#,
        "hello\n5\n4\n",
    );
}

#[test]
fn the_right_of_a_coalesce_is_given_the_left_to_be() {
    check(
        "Coalesce",
        r#"
using System;
using System.Collections.Generic;

class Coalesce
{
    static int Count(List<int> given)
    {
        // Each right-hand side has no type of its own until the left says
        // what it should be.
        List<int> items = given ?? new();
        return items.Count;
    }

    static void Main()
    {
        int? missing = null;
        Console.WriteLine(missing ?? default);
        Console.WriteLine(Count(null));
        Func<int, int> twice = null;
        Func<int, int> chosen = twice ?? (x => x + x);
        Console.WriteLine(chosen(21));
    }
}
"#,
        "0\n0\n42\n",
    );
}

#[test]
fn a_lambda_inside_a_generic_type_is_named_through_the_construction() {
    check(
        "GenericLambda",
        r#"
using System;

class Pool<T> where T : class
{
    internal delegate T Factory();
    private readonly Factory _empty;
    private readonly Factory _made;

    internal Pool(Func<Pool<T>, T> factory)
    {
        // Captures nothing, so it stays a method of `Pool<T>` itself.
        _empty = () => null;
        // Captures `factory` and `this`, so it becomes a method of a display
        // class that is inside `Pool<T>` and therefore generic too.
        _made = () => factory(this);
    }

    internal T Empty() { return _empty(); }
    internal T Made() { return _made(); }
}

class GenericLambda
{
    static void Main()
    {
        Pool<string> pool = new Pool<string>(p => "made");
        Console.WriteLine(pool.Empty() == null);
        Console.WriteLine(pool.Made());
    }
}
"#,
        "True\nmade\n",
    );
}

#[test]
fn a_constraint_reaches_the_row_the_parameter_ended_up_in() {
    check(
        "Constraints2",
        r#"
using System;

class Holder<T>
{
    public T Value;
}

abstract class Visitor
{
    // An override may not restate the constraint, and the row still has to
    // carry it or the runtime calls it weaker than what it overrides.
    public abstract T Pick<T>(T given) where T : class;
}

class Picker : Visitor
{
    public override T Pick<T>(T given) { return given; }
}

class Marker { }

class Bound<T> where T : Marker
{
    public T Held;
}

class Constraints
{
    static void Main()
    {
        Holder<int> holder = new Holder<int>();
        holder.Value = 7;
        Console.WriteLine(holder.Value);
        Console.WriteLine(new Picker().Pick("kept"));
        Bound<Marker> bound = new Bound<Marker>();
        Console.WriteLine(bound.Held == null);
    }
}
"#,
        "7\nkept\nTrue\n",
    );
}

#[test]
fn a_name_that_is_both_a_type_and_a_member_reaches_the_static_through_the_type() {
    check(
        "ColorColor",
        r#"
using System;

class Palette
{
    public static Palette Make() { return new Palette(); }
    public string Name;
}

class Holder
{
    // The property and the type go by the same name, which §12.8.7.2 allows:
    // a static member is reached through the type and an instance member
    // through the property, and the two spellings are identical.
    public Palette Palette { get; set; }

    public string Both()
    {
        Palette made = Palette.Make();
        made.Name = "made";
        Palette = made;
        return Palette.Name;
    }
}

class ColorColor
{
    static void Main() { Console.WriteLine(new Holder().Both()); }
}
"#,
        "made\n",
    );
}

#[test]
fn a_params_array_goes_after_the_optionals_it_follows() {
    check(
        "ParamsLast",
        r#"
using System;

class Describe
{
    public string Text;
    public Describe(string id, string category, bool enabled,
                    string description = null, string link = null,
                    params string[] tags)
    {
        Text = id + "/" + category + "/" + enabled + "/" + (description ?? "-")
             + "/" + (link ?? "-") + "/" + tags.Length;
    }
}

class ParamsLast
{
    static void Main()
    {
        // Three written, two optional left out, and the array last: putting
        // it where the first optional goes passes it as the wrong parameter.
        Console.WriteLine(new Describe("SP0001", "here", true).Text);
        Console.WriteLine(new Describe("SP0002", "there", false, "why", "how", "a", "b").Text);
    }
}
"#,
        "SP0001/here/True/-/-/0\nSP0002/there/False/why/how/2\n",
    );
}

#[test]
fn a_lambda_takes_by_reference_where_its_delegate_does() {
    check(
        "RefLambda",
        r#"
using System;

struct Counter
{
    internal int Value;
    internal bool Above(int limit) { return Value > limit; }
}

delegate bool Test(ref Counter counter, int limit);

class RefLambda
{
    static bool Run(Test test, ref Counter counter, int limit)
    {
        return test(ref counter, limit);
    }

    static void Main()
    {
        // The lambda becomes a method whose first parameter is `Counter&`:
        // anything else and the delegate cannot be built from it.
        Test test = (ref Counter counter, int limit) =>
        {
            counter.Value = counter.Value + 1;
            return counter.Above(limit);
        };
        Counter counter = new Counter();
        counter.Value = 5;
        Console.WriteLine(Run(test, ref counter, 5));
        Console.WriteLine(counter.Value);
    }
}
"#,
        "True\n6\n",
    );
}

#[test]
fn a_by_value_call_does_not_reach_the_overload_that_takes_it_by_reference() {
    check(
        "RefOverload",
        r#"
using System;

class RefOverload
{
    // The two differ only in how the argument travels, which the argument
    // types alone cannot tell apart.
    static int Step(ref int value) { value = value + 1; return value; }
    static int Step(int value) { return value + 10; }

    static void Main()
    {
        int value = 1;
        Console.WriteLine(Step(value));
        Console.WriteLine(value);
        Console.WriteLine(Step(ref value));
        Console.WriteLine(value);
    }
}
"#,
        "11\n1\n2\n2\n",
    );
}

#[test]
fn a_default_argument_is_read_in_the_scope_it_was_written_in() {
    check(
        "DefaultScope",
        r#"
using System;

namespace Inner
{
    enum Mode { None = 0, Syntax = 1, Directive = 2 }

    static class Work
    {
        // `Mode` is a name of this namespace and of nowhere else, so a caller
        // outside it cannot read this line — and still has to take its value.
        internal static int Run(int times, Mode mode = Mode.Directive)
        {
            return times * (int)mode;
        }
    }
}

class DefaultScope
{
    static void Main()
    {
        Console.WriteLine(Inner.Work.Run(10));
    }
}
"#,
        "20\n",
    );
}

#[test]
fn an_array_of_two_dimensions_is_reached_through_the_members_the_runtime_gives_it() {
    check(
        "Rectangular",
        r#"
using System;

class Rectangular
{
    static readonly int[,] Table = new int[3, 4];

    static void Add(ref int slot, int by) { slot = slot + by; }

    static void Main()
    {
        for (int row = 0; row < 3; row++)
        {
            for (int column = 0; column < 4; column++)
            {
                Table[row, column] = row * 10 + column;
            }
        }
        Console.WriteLine(Table[2, 3]);
        Table[1, 1] += 100;
        Console.WriteLine(Table[1, 1]);
        // `ref` to an element goes through `Address`, which is the third of
        // the members the runtime supplies.
        Add(ref Table[0, 2], 5);
        Console.WriteLine(Table[0, 2]);

        // `int[][,]` is a vector of two-dimensional arrays: the leftmost rank
        // is the outermost one.
        int[][,] nested = new int[2][,];
        nested[0] = new int[1, 2];
        nested[1] = Table;
        nested[0][0, 1] = 9;
        Console.WriteLine(nested[0][0, 1]);
        Console.WriteLine(nested[1][2, 3]);

        // One brace per dimension, read across the rows.
        byte[,] written = new byte[,]
        {
            { 1, 2, 3 },
            { 4, 5, 6 },
        };
        Console.WriteLine(written[0, 2]);
        Console.WriteLine(written[1, 0]);
    }
}
"#,
        "23\n111\n7\n9\n23\n3\n4\n",
    );
}

#[test]
fn a_partial_type_gets_no_constructor_of_its_own_when_a_later_part_writes_one() {
    check(
        "PartialConstructor",
        r#"
using System;

abstract class Node
{
    protected Node(int kind) { Kind = kind; }
    internal int Kind;
}

// This part declares no constructor. Whether the type has one is not
// answerable here — the part that writes it comes below.
partial class Leaf
{
    internal static Leaf Make(int kind) { return new Leaf(kind); }
}

partial class Leaf : Node
{
    internal Leaf(int kind) : base(kind) { }
}

class PartialConstructor
{
    static void Main()
    {
        Console.WriteLine(Leaf.Make(7).Kind);
    }
}
"#,
        "7\n",
    );
}

#[test]
fn a_generic_type_reads_the_static_its_own_initializer_wrote() {
    check(
        "GenericStatic",
        r#"
using System;

class Box<T>
{
    private static readonly string s_name = "made";
    internal static string Name() { return s_name; }
}

class Counted<T>
{
    private static readonly int s_start;
    private static int s_next = 7;

    // A written class constructor runs the field initializers first, and is
    // the only `.cctor` the type has.
    static Counted() { s_start = s_next + 1; }

    internal static int Start() { return s_start; }
}

class GenericStatic
{
    static void Main()
    {
        Console.WriteLine(Box<int>.Name());
        Console.WriteLine(Box<string>.Name());
        Console.WriteLine(Counted<int>.Start());
    }
}
"#,
        "made\nmade\n8\n",
    );
}

#[test]
fn a_local_function_reads_the_variables_of_the_method_that_holds_it() {
    check(
        "CapturingLocal",
        r#"
using System;

class CapturingLocal
{
    private int _base = 100;

    int Run(int start)
    {
        int running = start;

        // Reads a local, a parameter and `this`, and writes the local back.
        int Step(int by)
        {
            running = running + by + start + _base;
            return running;
        }

        Step(1);
        Step(2);
        // A lambda beside it reads the same local, through the same field.
        Func<int> read = () => running;
        return read();
    }

    static void Main()
    {
        Console.WriteLine(new CapturingLocal().Run(10));
    }
}
"#,
        "233\n",
    );
}

#[test]
fn an_in_parameter_is_a_reference_the_call_site_need_not_write() {
    check(
        "InParameter",
        r#"
using System;

struct Window
{
    internal int Position;
    internal void Advance() { Position = Position + 1; }
    internal int Peek() { return Position; }
}

class Reader
{
    // A field of a reference type, so a call on it has to reach the field
    // itself rather than a copy of it.
    internal Window Window;

    static int Width(in Window window) { return window.Position * 10; }

    internal int Run()
    {
        Window.Advance();
        Window.Advance();
        // Neither call site writes `in`, and both still pass a reference.
        return Width(Window) + Width(in Window) + Window.Peek();
    }
}

class InParameter
{
    static void Main()
    {
        Console.WriteLine(new Reader().Run());
    }
}
"#,
        "42\n",
    );
}

#[test]
fn an_automatic_property_runs_the_initializer_it_was_given() {
    check(
        "PropertyInitializer",
        r#"
using System;

class Holder
{
    internal static string Shared { get; } = "shared";
    internal int Count { get; set; } = 7;
    internal string Name { get; } = "named";
}

class PropertyInitializer
{
    static void Main()
    {
        Holder holder = new Holder();
        Console.WriteLine(Holder.Shared);
        Console.WriteLine(holder.Count);
        Console.WriteLine(holder.Name);
        holder.Count = holder.Count + 1;
        Console.WriteLine(holder.Count);
    }
}
"#,
        "shared\n7\nnamed\n8\n",
    );
}

#[test]
fn a_constructor_initializer_may_name_the_parameter_it_fills() {
    check(
        "NamedBase",
        r#"
using System;

class Text
{
    internal int Algorithm;
    internal string Container;

    protected Text(int algorithm = 1, string container = "none")
    {
        Algorithm = algorithm;
        Container = container;
    }
}

class SubText : Text
{
    internal SubText(string container)
        : base(container: container)
    {
    }
}

class NamedBase
{
    static void Main()
    {
        SubText text = new SubText("held");
        Console.WriteLine(text.Algorithm);
        Console.WriteLine(text.Container);
    }
}
"#,
        "1\nheld\n",
    );
}

#[test]
fn an_expression_bodied_constructor_runs_its_expression_and_returns_nothing() {
    check(
        "ArrowConstructor",
        r#"
using System;

class Holder
{
    private readonly int _value;

    // `=> e` on a constructor is a statement, not a return: a constructor
    // gives nothing back, whatever the thing it makes is.
    internal Holder(int value) => _value = value;

    internal int Value() { return _value; }
}

class ArrowConstructor
{
    static void Main()
    {
        Console.WriteLine(new Holder(9).Value());
    }
}
"#,
        "9\n",
    );
}

#[test]
fn an_inherited_field_belongs_to_the_base_as_the_receiver_constructs_it() {
    check(
        "InheritedField",
        r#"
using System;

class Entry<TKey, TValue>
{
    internal TKey Key;
    internal TValue Value;
}

abstract class CachingBase<TEntry>
{
    protected readonly int Mask;
    protected TEntry[] Entries;
    protected int Size => Entries.Length;

    internal CachingBase(int size)
    {
        Mask = size - 1;
        Entries = new TEntry[size];
    }
}

class Factory<TKey, TValue> : CachingBase<Entry<TKey, TValue>>
{
    internal Factory(int size) : base(size) { }

    // `Mask`, `Entries` and `Room` are `CachingBase<Entry<TKey, TValue>>`'s,
    // not this type's: naming them through this type names members it has
    // not.
    internal int Room() { return Mask + Entries.Length + Size; }
}

class InheritedField
{
    static void Main()
    {
        Console.WriteLine(new Factory<string, int>(8).Room());
    }
}
"#,
        "23\n",
    );
}

#[test]
fn an_unsigned_right_shift_never_carries_the_sign() {
    check(
        "UnsignedShift",
        r#"
using System;

class UnsignedShift
{
    static void Main()
    {
        int value = -16;
        Console.WriteLine(value >> 2);
        Console.WriteLine(value >>> 28);
        int running = -16;
        running >>>= 28;
        Console.WriteLine(running);
    }
}
"#,
        "-4\n15\n15\n",
    );
}

#[test]
fn a_method_group_reaches_only_the_overload_that_wants_a_delegate() {
    check(
        "GroupOverload",
        r#"
using System;

delegate bool Compare(int left, int right);

interface IOrder { }

class GroupOverload
{
    // The two differ only in what the last parameter is, and a method named
    // without being called fits the delegate and nothing else.
    static string Sort(int[] values, Compare compare) { return "delegate"; }
    static string Sort(int[] values, IOrder order) { return "order"; }

    static bool Ascending(int left, int right) { return left < right; }

    static void Main()
    {
        Console.WriteLine(Sort(new int[0], Ascending));
    }
}
"#,
        "delegate\n",
    );
}

#[test]
fn this_inside_a_struct_is_a_value_where_a_value_is_wanted() {
    check(
        "StructThis2",
        r#"
using System;

struct Walker
{
    internal int Count;

    // `this` is an address inside a struct's method, and what `new
    // Reader(this)` takes is what the struct holds.
    internal Reader Read() { return new Reader(this); }
}

struct Reader
{
    private readonly Walker _over;
    internal Reader(Walker over) { _over = over; }
    internal int Count() { return _over.Count; }
}

class StructThis
{
    static void Main()
    {
        Walker walker = new Walker();
        walker.Count = 5;
        Console.WriteLine(walker.Read().Count());
    }
}
"#,
        "5\n",
    );
}

#[test]
fn a_type_pattern_does_not_match_the_null_that_has_that_type() {
    check(
        "NullTypePattern",
        r#"
class Holder
{
    public int Kind;
}

class Program
{
    static Holder Next(int rounds)
    {
        return rounds >= 2 ? null : new Holder();
    }

    static void Main()
    {
        Holder nothing = null;
        // The static type says `Holder`, and a null is one — but it is not a
        // value any type pattern matches.
        System.Console.WriteLine(nothing is Holder named ? "yes" : "no");
        System.Console.WriteLine(nothing is Holder ? "yes" : "no");
        int rounds = 0;
        while (Next(rounds) is Holder held)
        {
            rounds = rounds + 1;
            if (rounds > 5) { System.Console.WriteLine("looped"); return; }
        }
        System.Console.WriteLine(rounds);
    }
}
"#,
        "no\nno\n2\n",
    );
}

#[test]
fn a_property_of_a_struct_field_writes_where_the_struct_lives() {
    check(
        "PackedField",
        r#"
struct Packed
{
    private ushort data;

    public byte Count
    {
        get { return (byte)(data >> 12); }
        set { data = (ushort)((data & 0x0FFF) | (value << 12)); }
    }
}

class Node
{
    private Packed packed;

    // The setter is called on where `packed` lives, not on a copy of it.
    public int Count
    {
        get { return packed.Count; }
        set { packed.Count = (byte)value; }
    }
}

class Program
{
    static void Main()
    {
        Node node = new Node();
        node.Count = 3;
        System.Console.WriteLine(node.Count);

        Packed[] row = new Packed[2];
        row[1].Count = 7;
        System.Console.WriteLine(row[1].Count);
        System.Console.WriteLine(row[0].Count);
    }
}
"#,
        "3\n7\n0\n",
    );
}

#[test]
fn an_overload_is_picked_by_the_conversion_the_argument_needs() {
    check(
        "BetterTarget",
        r#"
class Program
{
    static string Take(decimal value) { return "decimal"; }
    static string Take(long value) { return "long"; }
    static string Take(int value) { return "int"; }
    static string Take(uint value) { return "uint"; }

    static string Wide(double value) { return "double"; }
    static string Wide(float value) { return "float"; }

    static void Main()
    {
        ushort width = 7;
        // `int` is reachable from every other candidate and reaches none of
        // them, which makes it the one the argument converts to best.
        System.Console.WriteLine(Take(width));
        int count = 1;
        System.Console.WriteLine(Take(count));
        long total = 1;
        System.Console.WriteLine(Take(total));
        System.Console.WriteLine(Wide(width));
    }
}
"#,
        "int\nint\nlong\nfloat\n",
    );
}

#[test]
fn a_generic_local_function_is_called_with_the_types_it_was_written_with() {
    check(
        "GenericLocal",
        r#"
class Base
{
    public virtual string Name { get { return "base"; } }
}

class Derived : Base
{
    public override string Name { get { return "derived"; } }
}

class Program
{
    static void Main()
    {
        // No argument says what `T` is, so the call has to.
        System.Console.WriteLine(Name<Derived>());
        System.Console.WriteLine(Pick<Derived>(out string held) + " " + held);

        // `new T()` has no constructor to call until `T` is known, and the
        // local `made` is of a type the method holding it cannot name.
        string Name<T>() where T : Base, new()
        {
            T made = new T();
            return made.Name;
        }

        bool Pick<T>(out string result) where T : Base, new()
        {
            result = new T().Name;
            return true;
        }
    }
}
"#,
        "derived\nTrue derived\n",
    );
}

#[test]
fn a_type_parameter_constrained_to_struct_is_zeroed_rather_than_made() {
    check(
        "NewOfAStruct",
        r#"
struct Counted
{
    public int Value;
}

class Program
{
    static int Zero<T>() where T : struct
    {
        T made = new T();
        return made.Equals(default(T)) ? 0 : 1;
    }

    static void Main()
    {
        System.Console.WriteLine(Zero<Counted>());
    }
}
"#,
        "0\n",
    );
}

#[test]
fn a_conditional_whose_branches_have_no_type_takes_the_one_it_is_given() {
    check(
        "TargetedConditional",
        r#"
using System;
using System.Collections.Generic;

class Program
{
    static void Main()
    {
        bool flag = true;
        // Neither branch has a type of its own, so what the conditional is
        // converted to is what types both of them.
        Func<int, int> step = flag ? n => n + 1 : n => n - 1;
        Console.WriteLine(step(1));
        Func<int, int> back = flag ? static n => n - 1 : static n => n + 1;
        Console.WriteLine(back(1));
        List<int> list = flag ? [1, 2] : [3];
        Console.WriteLine(list.Count);
        // One that does have a type of its own still decides for itself.
        string text = flag ? "a" : null;
        Console.WriteLine(text);
    }
}
"#,
        "2\n0\n2\na\n",
    );
}

#[test]
fn a_method_group_written_bare_carries_the_receiver_it_did_not_write() {
    check(
        "BareMethodGroup",
        r#"
using System;

class Program
{
    int seed = 5;

    int Twice(int n) { return n * 2 + seed; }

    void Run()
    {
        // Both of these name instance methods, and a delegate to one may not
        // be made over a null: the `this` nobody wrote is what it closes over.
        Func<int, int> declared = Twice;
        Func<int, int> local = Thrice;
        Console.WriteLine(declared(3));
        Console.WriteLine(local(3));
        int Thrice(int n) { return n * 3 + seed; }
    }

    static int Half(int n) { return n / 2; }

    static void Main()
    {
        new Program().Run();
        Func<int, int> halved = Half;
        Func<int, int> counted = Count;
        Console.WriteLine(halved(8));
        Console.WriteLine(counted(8));
        int Count(int n) { return n + 1; }
    }
}
"#,
        "11\n14\n4\n9\n",
    );
}

#[test]
fn a_local_function_in_a_display_class_becomes_a_delegate_over_it() {
    check(
        "DisplayGroup",
        r#"
using System;

class Program
{
    static void Main()
    {
        int seed = 10;
        // The capturing lambda is what makes a display class; the local
        // functions of the same method live in it too, so a delegate to one
        // closes over the class rather than over a null.
        Func<int, int> add = n => n + seed;
        Func<int, int> step = Twice;
        Func<int, int> flat = Thrice;
        Console.WriteLine(add(1));
        Console.WriteLine(step(3));
        Console.WriteLine(flat(3));
        Console.WriteLine(Twice(4));
        int Twice(int n) { return n * 2 + seed; }
        static int Thrice(int n) { return n * 3; }
    }
}
"#,
        "11\n16\n9\n18\n",
    );
}

#[test]
fn a_list_pattern_counts_the_elements_and_looks_at_them() {
    check(
        "ListPatterns",
        r#"
using System;
using System.Collections.Generic;

class Program
{
    static string Array(int[] values)
    {
        if (values is [1, 2, 3]) { return "one two three"; }
        if (values is [int only]) { return "only " + only; }
        if (values is [1, .., 9]) { return "one to nine"; }
        if (values is []) { return "empty"; }
        return "other";
    }

    static string Counted(List<string> values)
    {
        // A `List<T>` says how many with `Count` and gives one with `this[int]`.
        return values is ["a", _] ? "a and one more" : "no";
    }

    static void Main()
    {
        Console.WriteLine(Array(new int[] { 1, 2, 3 }));
        Console.WriteLine(Array(new int[] { 7 }));
        Console.WriteLine(Array(new int[] { 1, 4, 5, 9 }));
        Console.WriteLine(Array(new int[] { }));
        Console.WriteLine(Array(new int[] { 2, 2 }));
        Console.WriteLine(Array(null));
        List<string> two = new List<string>();
        two.Add("a");
        two.Add("b");
        Console.WriteLine(Counted(two));
        // A string is a list of its characters.
        Console.WriteLine("abc" is ['a', _, 'c'] ? "yes" : "no");
    }
}
"#,
        "one two three\nonly 7\none to nine\nempty\nother\nother\na and one more\nyes\n",
    );
}

#[test]
fn a_case_label_that_names_a_type_is_a_test_and_not_a_comparison() {
    check(
        "CaseType",
        r#"
using System;

enum Shade { Red = 1, Blue = 2 }

class Program
{
    static string Describe(object value)
    {
        // `case string:` and `case Shade.Red:` are written the same way, and
        // only what the name means tells one from the other.
        switch (value)
        {
            case string: return "text";
            case int: return "number";
            default: return "other";
        }
    }

    static string Shaded(Shade shade)
    {
        switch (shade)
        {
            case Shade.Red: return "red";
            default: return "not red";
        }
    }

    static void Main()
    {
        Console.WriteLine(Describe("a"));
        Console.WriteLine(Describe(1));
        Console.WriteLine(Describe(new object()));
        Console.WriteLine(Shaded(Shade.Red));
        Console.WriteLine(Shaded(Shade.Blue));
    }
}
"#,
        "text\nnumber\nother\nred\nnot red\n",
    );
}

#[test]
fn a_constant_zero_is_a_value_of_every_enum() {
    check(
        "EnumZero",
        r#"
using System;

enum Level { Low = 0, High = 1 }

class Program
{
    static string Take(Level level) { return level == Level.Low ? "low" : "high"; }

    static void Main()
    {
        // Zero is a value of every enum, named or not (§10.2.4).
        Console.WriteLine(Take(0));
        Level none = 0;
        Console.WriteLine(none == Level.Low);
        Console.WriteLine(Take(Level.High));
    }
}
"#,
        "low\nTrue\nhigh\n",
    );
}

#[test]
fn a_constructor_chains_to_a_base_that_fills_its_own_arguments() {
    check(
        "BaseDefaults",
        r#"
using System;

class Holder
{
    public int Seed;
    internal Holder(int seed = 5) { Seed = seed; }
}

class First : Holder
{
    // No `: base(...)` written, and the base takes something it fills itself.
    public First() { }
}

class Second : Holder
{
    public Second() : base(7) { }
}

class Program
{
    static void Main()
    {
        Console.WriteLine(new First().Seed);
        Console.WriteLine(new Second().Seed);
    }
}
"#,
        "5\n7\n",
    );
}

#[test]
fn a_method_group_in_a_branch_is_typed_by_what_the_whole_thing_is_given_to() {
    check(
        "GroupInBranch",
        r#"
using System;

class Holder
{
    public void Close() { Console.WriteLine("gone"); }
}

class Program
{
    static void Main()
    {
        Holder holder = new Holder();
        // A method group has no type of its own and no syntax that says so:
        // this reads like two values, and only the target tells them apart.
        Action onDispose = false ? null : holder.Close;
        onDispose();
        Action nothing = true ? null : holder.Close;
        Console.WriteLine(nothing == null);
    }
}
"#,
        "gone\nTrue\n",
    );
}

#[test]
fn a_class_the_compiler_makes_carries_the_type_parameters_it_holds_values_of() {
    check(
        "GenericHolders",
        r#"
using System;
using System.Collections.Generic;

class Outer<T>
{
    private T only;

    public Outer(T value) { only = value; }

    // A state machine nested in a generic type holds values of its parameter.
    public IEnumerable<T> Twice()
    {
        yield return only;
        yield return only;
    }
}

class Program
{
    // A lambda capturing the method's own `T` needs a class that declares it.
    static Func<T> Held<T>(T value)
    {
        return () => value;
    }

    // So does a state machine for a generic method.
    static IEnumerable<T> Pair<T>(T value)
    {
        yield return value;
        yield return value;
    }

    static void Main()
    {
        foreach (string s in new Outer<string>("a").Twice()) { Console.WriteLine(s); }
        Console.WriteLine(Held<int>(5)());
        Console.WriteLine(Held<string>("b")());
        foreach (int n in Pair<int>(7)) { Console.WriteLine(n); }
    }
}
"#,
        "a\na\n5\nb\n7\n7\n",
    );
}

/// A type nested in a generic one is generic in metadata even where it writes
/// no parameters of its own, so its static members belong to a construction
/// and cannot be named by their definitions.
#[test]
fn a_static_member_of_a_type_nested_in_a_generic_one_is_reached_through_it() {
    check(
        "NestedStatics",
        r#"
using System;

class Pool<T>
{
    // Writes no type parameters, yet metadata gives it `T`.
    private class Shared
    {
        public static int Count = 7;

        public static int Twice() { return Count * 2; }
    }

    public int Read() { return Shared.Count; }

    public int Doubled() { return Shared.Twice(); }

    private class Inner
    {
        // From further in, the same parameters are still the ones in scope.
        public static int Reach() { return Shared.Count + 1; }
    }

    public int FromInner() { return Inner.Reach(); }
}

class Program
{
    static void Main()
    {
        Pool<string> pool = new Pool<string>();
        Console.WriteLine(pool.Read());
        Console.WriteLine(pool.Doubled());
        Console.WriteLine(pool.FromInner());
        Console.WriteLine(new Pool<int>().Read());
    }
}
"#,
        "7\n14\n8\n7\n",
    );
}

/// A base class's member can be what answers an interface a derived class
/// lists, and the CLI fills an interface slot only from a virtual method.
#[test]
fn a_base_class_member_answers_an_interface_the_derived_class_lists() {
    check(
        "InheritedImplementation",
        r#"
using System;

interface IThing
{
    int Size { get; }

    string Name();
}

abstract class Base
{
    // Writes neither `virtual` nor an interface of its own, and is still what
    // `Thing` answers `IThing` with.
    public int Size { get { return 3; } }

    public string Name() { return "base"; }
}

class Thing : Base, IThing
{
}

class Program
{
    static void Main()
    {
        IThing thing = new Thing();
        Console.WriteLine(thing.Size);
        Console.WriteLine(thing.Name());
        Console.WriteLine(new Thing().Name());
    }
}
"#,
        "3\nbase\nbase\n",
    );
}

/// A static member inherited from a generic base belongs to the construction
/// the derived class wrote, and `!0` means nothing in a class that declares
/// no type parameters.
#[test]
fn a_static_member_of_a_generic_base_is_reached_through_what_the_class_wrote() {
    check(
        "StaticOfBase",
        r#"
using System;

class Base<T, U>
{
    protected struct Held { public T value; }

    protected static void Shared(int n) { Console.WriteLine("shared " + n); }

    protected static void Show(Held held) { Console.WriteLine("held " + held.value); }
}

class Derived : Base<string, int>
{
    public void Go()
    {
        Shared(7);
        Held held = new Held();
        held.value = "a";
        Show(held);
    }
}

class Program
{
    static void Main() { new Derived().Go(); }
}
"#,
        "shared 7\nheld a\n",
    );
}

/// A value read through `?.` is a `T?`: the whole expression has a null to
/// give back, and a struct has none of its own to be.
#[test]
fn a_value_type_read_through_a_question_mark_is_one_that_can_be_missing() {
    check(
        "ConditionalValue",
        r#"
using System;

class Holder
{
    public int Size() { return 3; }
}

class Program
{
    static void Main()
    {
        Holder held = new Holder();
        Holder missing = null;
        Console.WriteLine(held?.Size() ?? 0);
        Console.WriteLine(missing?.Size() ?? 0);
        int? maybe = missing?.Size();
        Console.WriteLine(maybe ?? 5);
        Console.WriteLine(held?.Size() == 3);
        if (missing?.Size() == null) { Console.WriteLine("yes"); }
    }
}
"#,
        "3\n0\n5\nTrue\nyes\n",
    );
}

/// §12.4.8 and §10.2.6: an operator and a conversion both have lifted forms,
/// where a missing operand gives back a missing answer.
#[test]
fn an_operator_on_a_value_that_can_be_missing_is_the_lifted_one() {
    check(
        "Lifted",
        r#"
using System;

struct Flags { public byte Count; }

class Node
{
    public Flags Info;
}

class Program
{
    static void Main()
    {
        Node node = new Node();
        node.Info.Count = 2;
        Node none = null;
        Console.WriteLine(node?.Info.Count > 0);
        Console.WriteLine(none?.Info.Count > 0);
        byte? small = 3;
        int? wide = small;
        Console.WriteLine(wide + 1);
        Console.WriteLine(node?.Info.Count + 1);
        int? a = 3;
        int? missing = null;
        Console.WriteLine(a > 2);
        Console.WriteLine(missing > 2);
        Console.WriteLine(a + 1);
        Console.WriteLine(missing + 1);
        Console.WriteLine(a == 3);
        Console.WriteLine(a == missing);
        Console.WriteLine(missing == null);
    }
}
"#,
        "True\nFalse\n4\n3\nTrue\nFalse\n4\n\nTrue\nFalse\nTrue\n",
    );
}

/// A lambda that writes its parameter types says what the method's type
/// arguments are, and an `out var` beside it says nothing until they are
/// known (§12.6.3.13).
#[test]
fn a_lambda_that_writes_its_parameters_settles_the_type_arguments() {
    check(
        "WrittenLambda",
        r#"
using System;

class Bound
{
    public static string Make<TKey, TArg, TValue>(
        Func<TKey, TArg, TValue> unbound, TArg argument, out TValue made)
        where TKey : class
    {
        made = unbound(null, argument);
        return typeof(TKey).Name + "/" + typeof(TArg).Name + "/" + typeof(TValue).Name;
    }
}

class Program
{
    static void Main()
    {
        Console.WriteLine(Bound.Make(static (string _, int held) => held + 1, 4, out var got));
        Console.WriteLine(got);
    }
}
"#,
        "String/Int32/Int32\n5\n",
    );
}

/// `x is null` on a `T?` asks whether it holds anything: a struct has no null
/// to branch on, and `brtrue` on one is not a program.
#[test]
fn a_null_pattern_on_a_value_that_can_be_missing_asks_whether_it_holds_one() {
    check(
        "NullPattern",
        r#"
using System;

enum Quick { A, B }

class Program
{
    static string Which(Quick? given)
    {
        if (given is null) { return "none"; }
        return given.Value.ToString();
    }

    static int Score(int? n) { return n switch { null => -1, 0 => 0, _ => 1 }; }

    static void Main()
    {
        Console.WriteLine(Which(null));
        Console.WriteLine(Which(Quick.B));
        Console.WriteLine(Score(null));
        Console.WriteLine(Score(0));
        Console.WriteLine(Score(7));
    }
}
"#,
        "none\nB\n-1\n0\n1\n",
    );
}

/// A `switch` expression whose arms are method groups has no type of its own:
/// what it is given to says what the arms are.
#[test]
fn a_switch_expression_takes_the_type_it_is_given_to() {
    check(
        "SwitchTargetTyped",
        r#"
using System;

enum Quick { A, B }

class Program
{
    static bool IsEven(int n) { return n % 2 == 0; }

    static bool IsOdd(int n) { return n % 2 != 0; }

    static void Main()
    {
        Quick which = Quick.B;
        Func<int, bool> chosen = which switch
        {
            Quick.A => IsEven,
            Quick.B => IsOdd,
            _ => throw new InvalidOperationException()
        };
        Console.WriteLine(chosen(3));
        bool local(int n) { return n > 2; }
        Func<int, bool> other = which switch { Quick.A => IsEven, _ => local };
        Console.WriteLine(other(3));
    }
}
"#,
        "True\nTrue\n",
    );
}

/// A lambda or a local function written in a generic method becomes a method
/// of the type, where the method's own type parameters mean nothing: it
/// declares them itself, and every call names them.
#[test]
fn a_lambda_or_local_function_in_a_generic_method_declares_its_parameters() {
    check(
        "GenericMethodLocals",
        r#"
using System;

class Program
{
    static string Describe<TKey, TValue>(TKey key, TValue value)
    {
        static string shape(TKey one, TValue two)
        {
            return typeof(TKey).Name + "/" + typeof(TValue).Name + "/" + one + "/" + two;
        }
        Func<TValue, string> show = held => typeof(TValue).Name + ":" + held;
        return shape(key, value) + "|" + show(value);
    }

    static string Nested<T>(T given)
    {
        static string inner<U>(U other)
        {
            return typeof(T).Name + "/" + typeof(U).Name + "/" + other;
        }
        return inner<int>(7) + "|" + inner<string>("a") + "|" + given;
    }

    static void Main()
    {
        Console.WriteLine(Describe("a", 1));
        Console.WriteLine(Describe(2, "b"));
        Console.WriteLine(Nested<double>(2.5));
    }
}
"#,
        "String/Int32/a/1|Int32:1\nInt32/String/2/b|String:b\nDouble/Int32/7|Double/String/a|2.5\n",
    );
}

/// What a class has comes from its base classes; an interface it implements
/// says what it must have, not what it has. A member found there would type
/// the expression as the interface's.
#[test]
fn a_member_of_an_interface_is_not_a_member_of_what_implements_it() {
    check(
        "ExplicitLookup",
        r#"
using System;

interface IChain
{
    IChain Up { get; }
}

partial class Node : IChain
{
    // Reachable only through `IChain`; `node.Up` is the one below.
    IChain IChain.Up => Above?.Deeper();
}

partial class Node
{
    internal Node Above;

    internal Node Up { get { return Above; } }

    internal Node Deeper() { return this; }
}

class Program
{
    static void Main()
    {
        Node root = new Node();
        Node child = new Node();
        child.Above = root;
        Console.WriteLine(((IChain)child).Up == root);
        Console.WriteLine(((IChain)root).Up == null);
        Console.WriteLine(child.Up == root);
    }
}
"#,
        "True\nTrue\nTrue\n",
    );
}

/// Inside a value type `this` is a `T&` argument like any other reference,
/// and `this = default` writes what it points at.
#[test]
fn a_struct_can_be_given_a_whole_new_value_through_this() {
    check(
        "AssignToThis",
        r#"
using System;

struct Info
{
    public int Count;

    public string Name;

    public Info(int count)
    {
        this = default;
        Count = count;
        Name = "made";
    }

    public void Clear() { this = default(Info); }
}

class Program
{
    static void Main()
    {
        Info info = new Info(3);
        Console.WriteLine(info.Count + "/" + info.Name);
        info.Clear();
        Console.WriteLine(info.Count + "/" + (info.Name == null));
    }
}
"#,
        "3/made\n0/True\n",
    );
}

/// §10.5.3: a cast may use an `op_Explicit` and nothing else may.
#[test]
fn a_cast_reaches_the_conversion_a_type_declared_for_it() {
    check(
        "ExplicitOperator",
        r#"
using System;

enum Kind { None = 0, First = 1 }

readonly struct Tag
{
    private readonly sbyte value;

    private Tag(int value) { this.value = (sbyte)value; }

    public static implicit operator Tag(Kind kind) { return new Tag((int)kind); }

    public static explicit operator Tag(int id) { return new Tag(id); }

    public static explicit operator int(Tag tag) { return tag.value; }

    public override string ToString() { return "Tag(" + value + ")"; }
}

class Program
{
    static void Main()
    {
        int i = 3;
        Tag made = (Tag)i;
        Console.WriteLine(made);
        Console.WriteLine((int)made);
        Tag lifted = Kind.First;
        Console.WriteLine(lifted);
        Console.WriteLine((int)(Tag)7);
    }
}
"#,
        "Tag(3)\n3\nTag(1)\n7\n",
    );
}

/// A call on a type parameter goes through `constrained.`, which reads a
/// pointer to the receiver whatever the parameter turns out to be.
#[test]
fn a_call_on_a_type_parameter_is_made_through_where_the_value_is() {
    check(
        "CallOnTypeParameter",
        r#"
using System;

class Program
{
    static int Combine<T>(T part, int current) where T : class
    {
        int hash = current * 17;
        if (part != null) { return hash + part.GetHashCode(); }
        return hash;
    }

    static string Show<T>(T given) { return given == null ? "none" : given.ToString(); }

    static string Both<T>(T given) where T : struct
    {
        return given.ToString() + "/" + given.GetHashCode();
    }

    static void Main()
    {
        Console.WriteLine(Combine("a", 1) == 17 + "a".GetHashCode());
        Console.WriteLine(Combine<string>(null, 1));
        Console.WriteLine(Show(5));
        Console.WriteLine(Show<string>(null));
        Console.WriteLine(Both(3));
    }
}
"#,
        "True\n17\n5\nnone\n3/3\n",
    );
}

/// §10.2.4 through a conditional: the `0` in `Private | (isStatic ? Static :
/// 0)` is a value of the enum on the other side, and so is the whole thing.
#[test]
fn a_conditional_with_a_constant_on_one_side_takes_the_other_sides_type() {
    check(
        "ConditionalConstant",
        r#"
using System;

enum Mods { None = 0, Private = 1, Static = 2 }

class Program
{
    static Mods Make(bool isStatic) { return Mods.Private | (isStatic ? Mods.Static : 0); }

    static Mods Other(bool isStatic) { return Mods.Private | (isStatic ? 0 : Mods.Static); }

    static void Main()
    {
        Console.WriteLine((int)Make(true));
        Console.WriteLine((int)Make(false));
        Console.WriteLine((int)Other(true));
    }
}
"#,
        "3\n1\n1\n",
    );
}

/// C# 8 gives interface members bodies: a class may leave a member to the
/// interface, a `sealed` or `private` one is no slot at all, a derived
/// interface can implement or re-abstract its base's explicitly, and an
/// interface keeps static state of its own.
#[test]
fn default_interface_members_answer_where_the_class_says_nothing() {
    check(
        "DefaultInterfaceMembers",
        r#"
using System;

interface IBase
{
    void Abstract();
    void Default() { Console.WriteLine("IBase.Default " + Helper()); }
    sealed void Sealed() { Console.WriteLine("IBase.Sealed"); }
    private int Helper() => Count;
    int Count => 1;
    static int Created;
    static void Note() { Created++; }
}

interface IDerived : IBase
{
    void IBase.Default() { Console.WriteLine("IDerived.Default"); }
    int IBase.Count => 2;
}

interface IAgain : IDerived
{
    abstract void IBase.Default();
}

class Plain : IBase
{
    public void Abstract() { Console.WriteLine("Plain.Abstract"); }
}

class Derived : IDerived
{
    public void Abstract() { IBase.Note(); }
}

class Again : IAgain
{
    public void Abstract() { }
    public void Default() { Console.WriteLine("Again.Default"); }
}

class Program
{
    static void Main()
    {
        IBase plain = new Plain();
        plain.Abstract();
        plain.Default();
        plain.Sealed();
        IBase derived = new Derived();
        derived.Default();
        derived.Abstract();
        Console.WriteLine(derived.Count + " " + IBase.Created);
        IBase again = new Again();
        again.Default();
    }
}
"#,
        "Plain.Abstract\nIBase.Default 1\nIBase.Sealed\nIDerived.Default\n2 1\nAgain.Default\n",
    );
}

/// A class that lists an interface its base class already answers is
/// answered by the member C# finds first, even one of a class in between
/// that the runtime would not look at: it gets a method of its own that
/// calls that member.
#[test]
fn a_class_listing_an_interface_again_is_answered_by_the_member_it_inherits() {
    check(
        "InterfaceListedAgain",
        r#"
using System;

interface IThing
{
    void Run();
}

class Base : IThing
{
    void IThing.Run() { Console.WriteLine("Base.IThing.Run"); }
}

class Middle : Base
{
    public void Run() { Console.WriteLine("Middle.Run"); }
}

class Again : Middle, IThing
{
}

class Program
{
    static void Main()
    {
        IThing thing = new Middle();
        thing.Run();
        thing = new Again();
        thing.Run();
    }
}
"#,
        "Base.IThing.Run\nMiddle.Run\n",
    );
}

/// A hot patch is a static method of a class of its own and cannot say
/// `base`: it calls a member on `PilotRuntime.Base.Of<B>(self)`, which is
/// made directly, as `base.M()` would be — not dispatched back to the
/// override that asked.
#[test]
fn a_call_on_base_of_is_made_as_base_makes_it() {
    check(
        "BaseOf",
        r#"
using System;
namespace PilotRuntime
{
    public static class Base
    {
        public static T Of<T>(object instance) where T : class => (T)instance;
    }
}
class Animal
{
    public virtual string Sound() => "...";
    public virtual string Name { get { return "animal"; } }
}
class Dog : Animal
{
    public override string Sound() => "woof";
    public override string Name { get { return "dog"; } }
}
static class Patch
{
    public static string Sound(Dog self) =>
        global::PilotRuntime.Base.Of<Animal>(self).Sound() + " then " + self.Sound();
    public static string Name(Dog self) =>
        global::PilotRuntime.Base.Of<Animal>(self).Name + "/" + self.Name;
}
class BaseOf
{
    static void Main()
    {
        var dog = new Dog();
        Console.WriteLine(Patch.Sound(dog));
        Console.WriteLine(Patch.Name(dog));
    }
}
"#,
        "... then woof\nanimal/dog\n",
    );
}

#[test]
fn a_using_inside_a_namespace_leans_on_the_usings_around_it() {
    // `using static SettingsPlayerPrefsKeys;` inside the namespace of a
    // system, with the class's namespace imported at the top of the file:
    // the directive is in the scope of the file's `using`s, which only the
    // ones beside it are not.
    check(
        "NestedUsing",
        r#"
using System;
using Game.Constants;
using Text = System.String;

namespace Game.Constants { public static class Keys { public const string Volume = "volume"; } }

namespace Game.Systems
{
    using static Keys;
    using Name = Text;

    static class Program
    {
        static void Main()
        {
            Name name = Volume;
            Console.WriteLine(name);
        }
    }
}
"#,
        "volume\n",
    );
}

#[test]
fn a_method_group_named_out_of_order_becomes_a_delegate() {
    // `CreateCheckpoint(p, r, radius: .., model: .., onEnterAction:
    // OnEnter)`: the arguments are evaluated as written and passed in
    // parameter order, and what is kept ahead of the call for that is a
    // value — of a group, the receiver it was written on, and the delegate
    // is made at the call once the overload says which.
    check(
        "ReorderedGroup",
        r#"
using System;
class Holder { public int N; public void Enter(int e) { Console.WriteLine("enter " + e + " on " + N); } }
class Program
{
    static int count;
    static Holder Next() { count++; Console.WriteLine("next " + count); return new Holder { N = count }; }
    static int Bump() { count += 10; Console.WriteLine("bump " + count); return count; }
    static void Make(int position, string text = "", int dimension = 0, Action<int> onEnter = null, Action<int> onExit = null)
    { onEnter?.Invoke(position); onExit?.Invoke(dimension); Console.WriteLine(text); }
    void Mine(int e) { Console.WriteLine("mine " + e); }
    void Run() { Make(3, onExit: Mine, dimension: 4, text: "v"); }
    static void Main()
    {
        Make(1, dimension: 2, text: "t", onEnter: Enter, onExit: _ => Console.WriteLine("exit"));
        Make(2, onEnter: Next().Enter, dimension: Bump(), text: "u");
        new Program().Run();
        void Enter(int e) { Console.WriteLine("enter " + e); }
    }
}
"#,
        "enter 1\nexit\nt\nnext 1\nbump 11\nenter 2 on 1\nu\nmine 4\nv\n",
    );
}

#[test]
fn a_parameter_shadows_a_namespace_of_its_name() {
    // `CopyTo<T>(T[] src, T[] des)` reads `src.Length` in a project where a
    // package declares `namespace src.Runtime`.
    check(
        "ParameterOverNamespace",
        r#"
namespace src.Runtime { public interface ILogger { } }
namespace Game
{
    static class Program
    {
        static int Count<T>(T[] src) => src.Length;
        static void Main() { System.Console.WriteLine(Count(new[] { 1, 2 })); }
    }
}
"#,
        "2\n",
    );
}

#[test]
fn a_generic_method_group_with_type_arguments_says_what_it_returns() {
    // `.Select(AssetDatabase.LoadAssetAtPath<GameObject>)`: nothing the
    // method takes mentions its type parameter, so what it returns, and
    // with it what `Select` makes, is what was written in the brackets.
    check(
        "GroupWithTypeArguments",
        r#"
using System;
class Asset { public string Name = "asset"; }
class Prefab : Asset { public string Kind = "prefab"; }
static class Db
{
    public static Asset Load(string path, Type type) => new Asset();
    public static T Load<T>(string path) where T : Asset, new() => new T();
}
static class Program
{
    static R[] Map<T, R>(T[] items, Func<T, R> map)
    {
        var mapped = new R[items.Length];
        for (int i = 0; i < items.Length; i++) mapped[i] = map(items[i]);
        return mapped;
    }
    static void Main()
    {
        var loaded = Map(new[] { "a", "b" }, Db.Load<Prefab>);
        Console.WriteLine(loaded[1].Kind + " " + loaded.Length);
    }
}
"#,
        "prefab 2\n",
    );
}

#[test]
fn a_conditional_of_a_lambda_and_a_group_reaches_only_a_delegate() {
    // `items.Sort(reverse ? static (x, y) => Compare(y, x) : Compare)`:
    // `List<T>` declares `Sort(IComparer<T>)` before `Sort(Comparison<T>)`,
    // and the conditional, which has no type, was taken to reach the first.
    check(
        "ConditionalFunctions",
        r#"
using System;
interface IOrder<T> { int Compare(T x, T y); }
delegate int Comparison<T>(T x, T y);
class Items<T>
{
    public T[] All;
    public void Sort(IOrder<T> order) => Console.WriteLine("order");
    public void Sort(Comparison<T> comparison)
    {
        for (int i = 0; i < All.Length; i++)
            for (int j = i + 1; j < All.Length; j++)
                if (comparison(All[i], All[j]) > 0) { var t = All[i]; All[i] = All[j]; All[j] = t; }
    }
}
static class Program
{
    static int ByValue(int x, int y) => x - y;
    static void Show(Items<int> items) => Console.WriteLine(items.All[0] + "" + items.All[1] + items.All[2]);
    static void Main()
    {
        var items = new Items<int> { All = new[] { 2, 3, 1 } };
        foreach (var reverse in new[] { false, true })
        {
            items.Sort(reverse ? static (x, y) => ByValue(y, x) : ByValue);
            Show(items);
            items.Sort(reverse ? ByValue : (x, y) => ByValue(y, x));
            Show(items);
        }
    }
}
"#,
        "123\n321\n321\n123\n",
    );
}

/// An operator a generic base class declares is called with the base as the
/// derived type constructs it: `Pref<bool>` reaches `UserSetting<bool>`'s
/// `op_Implicit`, not one with its `T` left open.
#[test]
fn an_inherited_operator_is_called_on_the_base_the_type_constructs() {
    check(
        "InheritedOperator",
        r#"
using System;

class UserSetting<T>
{
    public T Value;
    public static implicit operator T(UserSetting<T> setting) => setting.Value;
}

class Pref<T> : UserSetting<T> { }

class Program
{
    static void Main()
    {
        var pref = new Pref<bool> { Value = true };
        if (pref) Console.WriteLine("on");
        bool b = pref;
        Console.WriteLine(b);
    }
}
"#,
        "on\nTrue\n",
    );
}

/// `null` given to a struct with an operator from a reference type is that
/// operator called with `null`, not the struct's default.
#[test]
fn null_given_to_a_struct_goes_through_its_operator() {
    check(
        "NullThroughOperator",
        r#"
using System;

class JsonObject { public string Id; }

struct JsonRef<T> where T : JsonObject
{
    public T Value;
    public string Tag;
    public static implicit operator JsonRef<T>(T value)
    {
        Console.WriteLine("op " + (value == null ? "null" : value.Id));
        return new JsonRef<T> { Value = value, Tag = "made" };
    }
}

class Program
{
    static void Main()
    {
        JsonRef<JsonObject> output = null;
        Console.WriteLine((output.Tag ?? "no tag") + " " + (output.Value == null));
    }
}
"#,
        "op null\nmade True\n",
    );
}

/// `'\xD800'` is a lone surrogate, as legal in C# as `'\uD800'`, and its
/// value is that code unit: Burst compares characters against both ends of
/// the surrogate range so.
#[test]
fn a_surrogate_character_literal_is_its_code_unit() {
    check(
        "SurrogateLiteral",
        r#"
using System;

class Program
{
    static void Main()
    {
        foreach (char value in new[] { 'a', (char)0xD801, (char)0xDFFF, (char)0xE000 })
        {
            Console.Write((value >= '\xD800' && value <= '\uDFFF') + " ");
        }
        Console.WriteLine((int)'\xD800');
    }
}
"#,
        "False True True False 55296\n",
    );
}

/// A base class's private nested type is not there for a derived class and
/// hides nothing (§12.5): Timeline's `SignalEmitterInspector` means the
/// namespace's `Styles`, not its base `MarkerInspector`'s own.
#[test]
fn a_bases_private_nested_type_hides_nothing_from_a_derived_class() {
    check(
        "PrivateNestedType",
        r#"
using System;

namespace N.Signals { static class Styles { public static string Icon = "signal"; } }

namespace N
{
    using N.Signals;

    class Marker
    {
        static class Styles { public static string Other = "marker"; }
        public static string M() => Styles.Other;
    }

    class Signal : Marker { public static string S() => Styles.Icon; }

    class Program { static void Main() { Console.WriteLine(Signal.S() + " " + Marker.M()); } }
}
"#,
        "signal marker\n",
    );
}

/// An `S?` boxes to whatever reference type `S` boxes to, a null to a null
/// (§10.2.9): Burst hands an `AssemblyOptions?` to `EnumPopup(Enum)`.
#[test]
fn a_nullable_enum_is_an_enum() {
    check(
        "NullableBoxing",
        r#"
using System;

enum Kind { A, B }

class Program
{
    static string Show(Enum e) => e == null ? "null" : e.ToString();

    static void Main()
    {
        Kind? k = Kind.B;
        Kind? n = null;
        Enum e = k;
        ValueType v = n;
        Console.WriteLine(Show(k) + " " + Show(n) + " " + e + " " + (v == null));
    }
}
"#,
        "B null B True\n",
    );
}

/// `new UnityAction(h)` with `h` an `Action` is a new delegate calling
/// `h.Invoke`, of the type written: R3's `FromEvent(h => new
/// UnityAction(h), …)` infers its delegate type from it.
#[test]
fn a_delegate_made_from_another_delegate_calls_it() {
    check(
        "DelegateFromDelegate",
        r#"
using System;

public delegate void UnityAction();
public delegate void UnityAction<T>(T x);

class Program
{
    static T Make<T>(Func<Action, T> conversion) => conversion(() => Console.WriteLine("made"));

    static void Main()
    {
        Action a = () => Console.WriteLine("a");
        var u = new UnityAction(a);
        u();
        Action<int> typed = i => Console.WriteLine("typed " + i);
        new UnityAction<int>(typed)(3);
        var made = Make(h => new UnityAction(h));
        made();
        Console.WriteLine(u.GetType().Name + " " + made.GetType().Name);
    }
}
"#,
        "a\ntyped 3\nmade\nUnityAction UnityAction\n",
    );
}

/// `base.M<T>()` where the base's base introduced `M` calls the base's
/// override, constructed with the caller's `T`: what it returns is that `T`,
/// and a `T` among its parameters still finds the override.
#[test]
fn a_generic_base_call_reaches_the_override_two_classes_up() {
    check(
        "GenericBaseCall",
        r#"
using System;

interface IResult { string Name { get; } }
class Result : IResult { public string Name => "result"; }

abstract class BuildScriptBase
{
    public TResult Build<TResult>(int input) where TResult : IResult => BuildData<TResult>(input);
    protected virtual TResult BuildData<TResult>(int input) where TResult : IResult => default;
    public abstract string Show<T>(T value);
}

class PackedMode : BuildScriptBase
{
    protected override TResult BuildData<TResult>(int input)
    {
        Console.WriteLine("packed " + input);
        return (TResult)(object)new Result();
    }
    public override string Show<T>(T value) => "packed " + value;
}

class Caching : PackedMode
{
    protected override TResult BuildData<TResult>(int input)
    {
        Console.WriteLine("caching");
        return base.BuildData<TResult>(input);
    }
    public override string Show<T>(T value) => "caching > " + base.Show<T>(value);
}

class Program
{
    static void Main()
    {
        var caching = new Caching();
        Console.WriteLine(caching.Build<IResult>(3).Name);
        Console.WriteLine(caching.Show(5));
    }
}
"#,
        "caching\npacked 3\nresult\ncaching > packed 5\n",
    );
}

/// A conditional between a method group and a delegate is that delegate:
/// the group has no type of its own for the other branch to reach (VFX's
/// `input ? container.GetOutputSlot : (Func<int, VFXSlot>)container.GetInputSlot`).
#[test]
fn a_conditional_of_a_method_group_and_a_delegate_is_the_delegate() {
    check(
        "ConditionalGroup",
        r#"
using System;

class Slot { public string Name; }

class Program
{
    Slot Out(int i) => new Slot { Name = "out" + i };
    Slot In(int i) => new Slot { Name = "in" + i };

    void Show(bool input)
    {
        var slots = input ? Out : (Func<int, Slot>)In;
        Console.WriteLine(slots(1).Name);
    }

    static void Main()
    {
        new Program().Show(true);
        new Program().Show(false);
    }
}
"#,
        "out1\nin1\n",
    );
}

/// `input ? null : () => …` says nothing of its own about what it is, and
/// is the delegate it is given to, an object initializer's member as much
/// as a local (the memory profiler's `InspectAction = compareMode ? null :
/// () => { … }`).
#[test]
fn a_conditional_of_null_and_a_lambda_is_the_delegate_it_is_given_to() {
    check(
        "ConditionalNullLambda",
        r#"
using System;

class Holder { public Action Inspect; public int Count; }

class Program
{
    static void Main()
    {
        foreach (var input in new[] { false, true })
        {
            var inspect = new Action(() => Console.WriteLine("inspected"));
            var holder = new Holder { Inspect = input ? null : () => { Console.Write("lambda "); inspect(); }, Count = 1 };
            Console.WriteLine(holder.Inspect == null);
            holder.Inspect?.Invoke();
        }
    }
}
"#,
        "False\nlambda inspected\nTrue\n",
    );
}

/// An array is no delegate, so a lambda never goes to `With(Column[])`, and
/// `With(Action<…>)` beside it is the call (Addressables' `TreeBuilder`).
#[test]
fn a_lambda_does_not_go_to_an_array_parameter() {
    check(
        "LambdaNotArray",
        r#"
using System;
using System.Collections.Generic;

struct Column { public string Name; }

class TreeBuilder
{
    public TreeBuilder With(Column[] columns) => this;
    public TreeBuilder With(Action<IEnumerable<object>> selected)
    {
        selected(new object[] { 1, 2 });
        return this;
    }
}

class Program
{
    static void Main()
    {
        new TreeBuilder().With(new Column[0]).With(items => { foreach (var item in items) Console.Write(item); });
        Console.WriteLine();
    }
}
"#,
        "12\n",
    );
}

/// A name is looked for in the types around the code before the classes
/// `using static` imports, and the first scope that has it is the one:
/// Animancer's `Lerp(a, b, t)` inside `Easing` is `Easing.Lerp`, though
/// `Mathf.Lerp` takes the same arguments. Only methods are called, though:
/// a field of the name leaves the call to the import.
#[test]
fn a_member_of_an_enclosing_type_comes_before_a_static_import() {
    check(
        "EnclosingBeforeStaticImport",
        r#"
using System;
using static Helpers;

static class Helpers
{
    public static float Lerp(float a, float b, float t) => -1;
    public static int Empty() => 7;
}

static class Easing
{
    public static float Lerp(float a, float b, float t) => a + (b - a) * t;

    public static class Quadratic
    {
        public static float Out(float a, float b, float t) => Lerp(a, b, t);
    }

    // A field is not called: `Empty()` beside it is the imported method.
    static readonly int Empty = Empty();

    static void Main() => Console.WriteLine(Quadratic.Out(0, 10, 0.5f) + " " + Empty);
}
"#,
        "5 7\n",
    );
}

#[test]
fn an_integer_constant_cast_to_a_float_type_is_rounded_to_it() {
    // `(float)16777217` is 16777216, so what is made of it afterwards is made
    // of that: the constants folded, and the same casts left to run, agree.
    check(
        "RoundedConstants",
        r"
using System;
class P {
    const int A = (int)(float)16777217;
    const long B = (long)(float)123456789;
    const double E = (float)16777217 + 0.0;
    const double F = (double)(float)123456789;
    const long G = unchecked((long)(float)9223372036854775807);
    const int H = unchecked((int)(float)2147483647);
    const float I = 16777217;
    const float J = 18446744073709551615;
    const double K = (double)9223372036854775807;
    const float O = 16777217 + 1f;
    const float O3 = 16777217L + 1f;
    const bool N = (float)0.1 == 0.1;
    const bool N2 = (float)0.1 == 0.1f;
    const double S2 = 0.1f + 0.2;
    const double U5 = (double)(9223372036854775807 - 1);
    static void Main() {
        Console.WriteLine(A);
        Console.WriteLine(B);
        Console.WriteLine(E);
        Console.WriteLine(F);
        Console.WriteLine(G);
        Console.WriteLine(H);
        Console.WriteLine((double)I);
        Console.WriteLine((double)J);
        Console.WriteLine(K);
        Console.WriteLine((double)O);
        Console.WriteLine((double)O3);
        Console.WriteLine(N);
        Console.WriteLine(N2);
        Console.WriteLine(S2);
        Console.WriteLine(U5);
        Console.WriteLine((int)(float)16777217);
        Console.WriteLine(unchecked((long)(float)9223372036854775807));
        Console.WriteLine((double)(float)123456789);
        Console.WriteLine((float)16777217 == 16777216f);
        Console.WriteLine((float)0.1 == 0.1);
        Console.WriteLine((double)(float)0.1);
        Console.WriteLine((double)(float)9007199254740993L);
        Console.WriteLine((double)(16777216f + 1 + 1));
        Console.WriteLine((double)(float)'a');
        int n = 16777217;
        Console.WriteLine((double)(float)n);
        Console.WriteLine((int)(float)n);
    }
}
",
        r"16777216
123456792
16777216
123456792
0
0
16777216
1.8446744073709552E+19
9.223372036854776E+18
16777216
16777216
False
True
0.30000000149011613
9.223372036854776E+18
16777216
0
123456792
True
False
0.10000000149011612
9007199254740992
16777216
97
16777216
16777216
",
    );
}

// MARK: - long flat chains

// Generated code is full of them: an `else if` for every case of a table, a
// `?:` for every row, a call for every step of a builder, a term for every
// piece of a string. Roslyn compiles five thousand of each, and so does
// this, through binding, definite assignment and emitting, with the
// program running to the same answer. The trees are as deep as the chains
// are long, and the compiler walks them on a stack of its own.

/// A program that runs `body` in `Main`, with `helpers` in the class around
/// it.
fn flat_program(helpers: &str, body: &str) -> String {
    format!(
        "using System;\nclass P\n{{\n{helpers}\nstatic int Main()\n{{\n{body}\nreturn 0;\n}}\n}}\n"
    )
}

#[test]
fn five_thousand_else_ifs_compile_and_run() {
    let n = 5000;
    let ladder: String = (1..n)
        .map(|i| format!("else if (x == {i}) x = {i};\n"))
        .collect();
    let source = flat_program(
        "",
        &format!(
            "int x = {}; if (x == 0) x = 0;\n{ladder}Console.WriteLine(x);",
            n - 3
        ),
    );
    check("ElseIfLadder", &source, "4997\n");
}

#[test]
fn a_five_thousand_link_ternary_ladder_compiles_and_runs() {
    let n = 5000;
    let ladder: String = (0..n).map(|i| format!("x == {i} ? {} : ", i * 2)).collect();
    let source = flat_program(
        "",
        &format!(
            "int x = {}; int y = {ladder}-1;\nConsole.WriteLine(y);",
            n - 3
        ),
    );
    check("TernaryLadder", &source, "9994\n");
}

#[test]
fn five_thousand_chained_calls_compile_and_run() {
    let source = flat_program(
        "",
        &format!(
            "int x = 7; string s = x.ToString(){};\nConsole.WriteLine(s);",
            ".ToString()".repeat(5000)
        ),
    );
    check("CallChain", &source, "7\n");
}

#[test]
fn a_five_thousand_term_sum_of_ints_compiles_and_runs() {
    let terms: String = (0..5000).map(|i| format!(" + {}", i % 7)).collect();
    let expected: i32 = 3 + (0..5000).map(|i| i % 7).sum::<i32>();
    let source = flat_program(
        "",
        &format!("int x = 3; int y = x{terms};\nConsole.WriteLine(y);"),
    );
    check("IntSum", &source, &format!("{expected}\n"));
}

#[test]
fn a_five_thousand_term_concatenation_of_strings_compiles_and_runs() {
    // Not constants: the compiler may not fold them.
    let source = flat_program(
        &format!("static string Join(string s) => s{};", " + s".repeat(5000)),
        "Console.WriteLine(Join(\"ab\").Length);",
    );
    check("StringSum", &source, &format!("{}\n", 5001 * 2));
}
