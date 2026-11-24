//! What the decompiler makes of programs whose source is known.
//!
//! Each program is compiled by rustlyn and read back; the output has to
//! contain the constructs the source used, spelled the way a reader would
//! expect, rather than the IL they became. A Roslyn-compiled fixture checks
//! the same against the other compiler's idioms.

use std::path::PathBuf;

use rustlyn_decompile::{Options, decompile, decompile_declared, decompile_with_references};
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

/// The .NET host, if there is one: `RUSTLYN_DOTNET`, `DOTNET_ROOT`, the
/// path, or a manual install under the home directory.
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

/// The newest shared framework next to the host.
fn framework() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("RUSTLYN_FRAMEWORK") {
        let path = PathBuf::from(path);
        return path.is_dir().then_some(path);
    }
    // `dotnet` on the path is often a link (Homebrew's is); the framework
    // is next to what it points at.
    let host = host()?;
    let root = std::fs::canonicalize(&host)
        .unwrap_or(host)
        .parent()?
        .to_path_buf();
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

/// Every assembly of the framework, as `-r` would have named them.
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

/// Compiles a program against the framework and decompiles the result, or
/// the part a filter names. Without a framework the test is skipped, with
/// an empty answer that satisfies nothing.
fn roundtrip(source: &str, filter: Option<&str>) -> Option<String> {
    let Some(bytes) = references() else {
        println!("note: skipped; no .NET shared framework was found");
        return None;
    };
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
    let compilation = Compilation::create_with_references(
        vec![parse(SourceText::new("Program.cs", source))],
        &images,
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
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    let emitted =
        rustlyn_emit::emit(&compilation, "Program").unwrap_or_else(|error| panic!("{error}"));
    let text = decompile_with_references(&emitted.assembly, &images, filter, &Options::default())
        .expect("readable");
    println!("{text}");
    Some(text)
}

/// Asserts that every snippet occurs in the text, in order.
fn expect(text: &str, snippets: &[&str]) {
    let mut at = 0;
    for snippet in snippets {
        match text[at..].find(snippet) {
            Some(found) => at += found + snippet.len(),
            None => panic!("expected `{snippet}` after position {at} in:\n{text}"),
        }
    }
}

#[test]
fn loops_come_back_as_loops() {
    let Some(text) = roundtrip(
        r"
using System;
using System.Collections.Generic;
class C
{
    static int Sum(int[] items, List<string> names)
    {
        int total = 0;
        for (int i = 0; i < items.Length; i++)
        {
            total += items[i];
        }
        foreach (var n in names)
        {
            if (n == null) continue;
            total += n.Length;
        }
        int k = 0;
        while (k < 10) { k++; if (k == 5) break; }
        do { k--; } while (k > 0);
        return total + k;
    }
    static void Main() { }
}",
        None,
    ) else {
        return;
    };
    expect(
        &text,
        &[
            "int num = 0;",
            "for (int i = 0; i < items.Length; i++)",
            "num += items[i];",
            "foreach (string name in names)",
            "if (name != null)",
            "num += name.Length;",
            "int num2 = 0;",
            "while (num2 < 10)",
            "num2++;",
            "if (num2 == 5)",
            "break;",
            "do",
            "num2--;",
            "while (num2 > 0);",
            "return num + num2;",
        ],
    );
}

#[test]
fn conditions_and_ternaries() {
    let Some(text) = roundtrip(
        r#"
class C
{
    static string Describe(int x, bool flag, string s)
    {
        string size = x > 10 ? "big" : "small";
        if (x == 1 || x == 2 && flag)
        {
            return size + "!";
        }
        return s ?? "none";
    }
    static bool Check(object o, double d)
    {
        if (o is string text) return text.Length > 0;
        return !(d < 1.0) && o != null;
    }
    static void Main() { }
}"#,
        None,
    ) else {
        return;
    };
    expect(
        &text,
        &[
            r#"string text = ((x > 10) ? "big" : "small");"#,
            "if (x == 1 || (x == 2 && flag))",
            r#"return text + "!";"#,
            r#"return s ?? "none";"#,
            "if (o is string text)",
            "return text.Length > 0;",
            "return !(d < 1.0) && o != null;",
        ],
    );
}

#[test]
fn exception_handling() {
    let Some(text) = roundtrip(
        r"
using System;
using System.IO;
class C
{
    static int Count;
    static string Read(string path)
    {
        string result = null;
        try
        {
            result = File.ReadAllText(path);
        }
        catch (IOException e) when (e.Message.Length > 0)
        {
            Console.WriteLine(e);
        }
        catch (Exception)
        {
            throw;
        }
        finally
        {
            Count++;
        }
        using (var reader = new StringReader(path))
        {
            reader.Read();
        }
        return result;
    }
    static void Main() { }
}",
        None,
    ) else {
        return;
    };
    expect(
        &text,
        &[
            "string result = null;",
            "try",
            "result = File.ReadAllText(path);",
            "catch (IOException ex) when (ex.Message.Length > 0)",
            "Console.WriteLine(ex);",
            "catch (Exception)",
            "throw;",
            "finally",
            "Count++;",
            "using (StringReader stringReader = new StringReader(path))",
            "stringReader.Read();",
            "return result;",
        ],
    );
}

#[test]
fn declarations_and_members() {
    let Some(text) = roundtrip(
        r#"
using System;
using System.Collections.Generic;
namespace Demo
{
    public enum Color { Red, Green = 5, Blue }
    public interface IShape { double Area { get; } }
    public abstract class Shape : IShape
    {
        public const int Max = 100;
        public static int Count;
        private readonly List<string> tags = new List<string>();
        public string Name { get; set; }
        public Color Color { get; private set; }
        protected Shape(string name) { Name = name; Count++; }
        public abstract double Area { get; }
        public virtual string Describe() => $"{Name}: {Area}";
        public override string ToString() => Describe();
        public static Shape operator +(Shape a, Shape b) => a;
        public int this[int i] { get { return i * 2; } }
        public event EventHandler Changed;
        public T First<T>(IEnumerable<T> items) where T : class
        {
            foreach (var item in items) return item;
            return null;
        }
    }
    public sealed class Circle : Shape
    {
        private readonly double radius;
        public Circle(double radius) : base("circle") { this.radius = radius; }
        public override double Area => Math.PI * radius * radius;
        public bool TryGet(out int value) { value = 3; return true; }
    }
    public struct Point
    {
        public int X;
        public int Y;
        public Point(int x, int y) { X = x; Y = y; }
    }
    static class Program { static void Main() { } }
}"#,
        None,
    ) else {
        return;
    };
    expect(
        &text,
        &[
            "namespace Demo",
            "public enum Color",
            "Red,",
            "Green = 5,",
            "Blue",
            "public interface IShape",
            "double Area { get; }",
            "public abstract class Shape : IShape",
            "public const int Max = 100;",
            "public static int Count;",
            "private readonly List<string> tags = new List<string>();",
            "public string Name { get; set; }",
            "public Color Color { get; private set; }",
            "public abstract double Area { get; }",
            "public int this[int i]",
            "return i * 2;",
            "public event EventHandler Changed;",
            "protected Shape(string name)",
            "Name = name;",
            "Count++;",
            "public virtual string Describe()",
            "return $\"{Name}: {Area}\";",
            "public override string ToString()",
            "return Describe();",
            "public static Shape operator +(Shape a, Shape b)",
            "public T First<T>(IEnumerable<T> items) where T : class",
            "foreach (T item in items)",
            "return item;",
            "public sealed class Circle : Shape",
            "private readonly double radius;",
            "public override double Area",
            "return Math.PI * radius * radius;",
            "public Circle(double radius) : base(\"circle\")",
            "this.radius = radius;",
            "public bool TryGet(out int value)",
            "value = 3;",
            "return true;",
            "public struct Point",
            "public Point(int x, int y)",
        ],
    );
}

#[test]
fn initializers_and_calls() {
    let Some(text) = roundtrip(
        r#"
using System;
using System.Collections.Generic;
class Item { public int Id; public string Name { get; set; } }
class C
{
    static void Main()
    {
        var item = new Item { Id = 1, Name = "a" };
        int[] numbers = { 1, 2, 3 };
        var list = new List<int>(numbers.Length);
        list.Add(numbers[0]);
        Console.WriteLine(item.Name + ":" + list.Count);
        Console.WriteLine(string.Format("{0} of {1}", item.Id, numbers.Length));
        Func<int, int> twice = v => v * 2;
        Console.WriteLine(twice(21));
        Console.WriteLine(typeof(Item).Name);
        Console.WriteLine(default(DateTime).Ticks);
    }
}"#,
        None,
    ) else {
        return;
    };
    expect(
        &text,
        &[
            r#"Item item = new Item { Id = 1, Name = "a" };"#,
            "int[] array = new int[3] { 1, 2, 3 };",
            "List<int> list = new List<int>(array.Length);",
            "list.Add(array[0]);",
            r#"Console.WriteLine(item.Name + ":" + list.Count);"#,
            r#"Console.WriteLine($"{item.Id} of {array.Length}");"#,
            "Console.WriteLine(func(21));",
            "typeof(Item).Name",
            "default(DateTime).Ticks",
        ],
    );
}

#[test]
fn a_roslyn_compiled_assembly_reads_the_same_way() {
    let bytes = std::fs::read(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/roslyn_sample.dll"
    ))
    .expect("fixture");
    let text = decompile(&bytes, Some("Point"), &Options::default()).expect("readable");
    println!("{text}");
    expect(
        &text,
        &[
            "public class Point",
            "private readonly List<string> names = new List<string>();",
            "public int Y { get; set; }",
            "for (int i = 0; i < items.Length; i++)",
            "foreach (string name in names)",
            "if (name != null && (name.Length <= 3 || name[0] != 'a'))",
            "if (o is string text)",
            r#"return "string " + text;"#,
            r#"string text2 = ((X > Y) ? "wide" : "tall");"#,
            "text2 += o.ToString();",
            "catch (InvalidOperationException ex) when (ex.Message.Length > 0)",
            "catch (Exception)",
            "throw;",
            "finally",
            "Count++;",
            r#"return text2 ?? "none";"#,
            "while (d > 1.0)",
            "d /= 2.0;",
            "do",
            "d++;",
            "while (d < 0.5);",
            // As it was written: `c == Color.Green && !flag || d != 0`.
            "return (c == Color.Green && !flag) || d != 0.0;",
            "using (IEnumerator<T> enumerator = xs.GetEnumerator())",
            "return enumerator.Current;",
            "return default(T);",
            "return $\"({X}, {Y})\";",
        ],
    );
}

/// The source of the second Roslyn fixture, compiled by rustlyn as well.
const FEATURES: &str = include_str!("fixtures/roslyn_features.cs");

/// What both compilers' output of the features fixture has to read as.
const FEATURE_SNIPPETS: &[&str] = &[
    "public IEnumerable<int> Evens(int[] data, int extra)",
    "int seen = 0;",
    "seen++;",
    "yield return",
    "if (seen >= limit)",
    "yield break;",
    "yield return -1;",
    "public IEnumerable<string> Lines(string path)",
    "using StreamReader reader = new StreamReader(path);",
    // Roslyn drops the name of a local that no `yield` keeps alive;
    // rustlyn hoists it under its own name.
    " = reader.ReadLine()) != null)",
    "yield return ",
    "finally",
    "Console.WriteLine(\"after\");",
    "public async Task<int> SumAsync(Task<int> a, Task<int> b)",
    "int x = await a;",
    "if (x > 10)",
    "return x;",
    "return x + await b.ConfigureAwait(continueOnCapturedContext: false) + limit;",
    "public async Task RunAsync()",
    "await Task.Delay(10);",
    "Console.WriteLine(\"done\");",
    "public List<int> Query(int[] data, int threshold)",
    "data.Where((int x) => x > threshold).Select((int x) => x * 2).ToList();",
    "Func<int, int> func = (int a) => a + threshold;",
    "threshold = 5;",
    "Console.WriteLine(func(1) + list.Count);",
    "public int Closures(int[] data)",
    "Func<int> func = () => d * limit + count;",
    "count += func();",
    "return count + Local(2);",
    "int Local(int v)",
    "return v * limit;",
    "public int? Length(Machines other)",
    "other?.RunAsync();",
    "name ??= \"x\";",
];

#[test]
fn state_machines_and_closures_from_roslyn() {
    let bytes = std::fs::read(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/roslyn_features.dll"
    ))
    .expect("fixture");
    let Some(references) = references() else {
        println!("note: skipped; no .NET shared framework was found");
        return;
    };
    let images: Vec<&[u8]> = references.iter().map(Vec::as_slice).collect();
    let text =
        decompile_with_references(&bytes, &images, None, &Options::default()).expect("readable");
    println!("{text}");
    expect(&text, FEATURE_SNIPPETS);
    // The machinery is folded away, not shown beside the methods.
    assert!(
        !text.contains("MoveNext"),
        "a state machine was left behind"
    );
    assert!(
        !text.contains("<>c__DisplayClass"),
        "a display class was left behind"
    );
}

#[test]
fn state_machines_and_closures_from_rustlyn() {
    let Some(text) = roundtrip(
        &format!("{FEATURES}\nstatic class Program {{ static void Main() {{ }} }}"),
        None,
    ) else {
        return;
    };
    expect(&text, FEATURE_SNIPPETS);
    assert!(
        !text.contains("MoveNext"),
        "a state machine was left behind"
    );
    assert!(
        !text.contains("<>c__DisplayClass"),
        "a display class was left behind"
    );
}

#[test]
fn a_lambda_holding_its_machine_is_not_the_machine() {
    // The lambda reaches `collected`, hoisted into the generic machine,
    // through a local that holds the machine. Taking that local for the
    // machine the lambda starts folded the method into its own lambda,
    // again and again, until the stack ran out.
    let Some(text) = roundtrip(
        r#"
using System;
using System.Threading.Tasks;
class Program
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

    static void Main() { Console.WriteLine(Go("!").Result); }
}
"#,
        None,
    ) else {
        return;
    };
    expect(
        &text,
        &[
            "async Task<string> Go<T>(T value)",
            "Func<string> describe = () =>",
        ],
    );
    assert_eq!(
        text.matches("async").count(),
        1,
        "the method was folded into its lambda"
    );
}

#[test]
fn a_constant_put_in_place_of_its_variable_keeps_the_variables_type() {
    // `0xFFFFFFFF` is loaded as the `int` -1; written where `u` was read,
    // it has to stay a `uint`, or `l += u` adds minus one.
    let Some(text) = roundtrip(
        r#"
class Program
{
    static void Main()
    {
        uint u = 0xFFFFFFFF;
        ulong ul = ulong.MaxValue;
        long l = 0;
        double d = 0;
        l += u;
        d += ul;
        System.Console.WriteLine(l + " " + d);
    }
}
"#,
        None,
    ) else {
        return;
    };
    expect(&text, &["uint.MaxValue", "ulong.MaxValue"]);
    assert!(!text.contains("+= -1"), "the constant lost its type");
}

#[test]
fn a_number_added_to_text_leaves_the_next_operand_alone() {
    // `u + " "` is a string: taken for a `uint`, it had the `sbyte` after it
    // cast to `uint`, and -1 printed as 4294967295.
    let Some(text) = roundtrip(
        r#"
class Program
{
    static void Main()
    {
        uint u = 3;
        sbyte s = -1;
        System.Console.WriteLine(u + " " + s);
    }
}
"#,
        None,
    ) else {
        return;
    };
    assert!(
        !text.contains("(uint)s"),
        "the sbyte was cast to the uint before it"
    );
    assert!(
        !text.contains("(uint)(sbyte)"),
        "the sbyte was cast to the uint before it"
    );
}

#[test]
fn what_the_stack_does_not_say_is_kept() {
    // A `bool` is a number on the stack, an implicit conversion a call, and
    // a filter whose type test was folded away a bare `return false`: each
    // came back meaning something else (`1` printed for `True`, a `Mask`
    // given to `+` unconverted, a filter that caught everything).
    let Some(text) = roundtrip(
        r#"
struct Mask
{
    public int value;
    public static implicit operator int(Mask m) => m.value;
}
class Program
{
    static void Main()
    {
        double d = double.NaN;
        Mask m = default;
        System.Console.WriteLine($"{d is double.NaN}");
        System.Console.WriteLine((int)m + " ");
        try
        {
            try { throw new System.Exception(); }
            catch (System.Exception) when (false) { System.Console.Write("unreachable"); }
        }
        catch { System.Console.WriteLine("outer"); }
    }
}
"#,
        None,
    ) else {
        return;
    };
    expect(&text, &["(int)", "catch when (", "catch"]);
    assert!(!text.contains("? 1 : 0"), "a bool came back a number");
    assert!(
        !text.contains("true)"),
        "a filter came back catching everything"
    );
    assert!(!text.contains("catch (object)"), "catch (object) is not C#");
}

#[test]
fn every_declaration_points_at_its_own_name() {
    let bytes = std::fs::read(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/roslyn_sample.dll"
    ))
    .expect("fixture");
    let (text, declared) = decompile_declared(&bytes, &[], &Options::default()).expect("readable");
    for declaration in &declared {
        let start = declaration.start as usize;
        let written = &text[start..start + declaration.length as usize];
        // A type is known by its metadata name, a constructor by its type's;
        // either way the text there is the name as C# writes it.
        let expected = declaration
            .name
            .rsplit(['.', '/'])
            .next()
            .unwrap_or(&declaration.name)
            .split('`')
            .next()
            .unwrap_or_default();
        assert_eq!(written, expected, "{declaration:?}");
    }
    let named = |name: &str, is_type: bool| {
        declared
            .iter()
            .find(|declaration| declaration.name == name && declaration.is_type == is_type)
    };
    assert!(named("Demo.Point", true).is_some(), "{declared:?}");
    assert!(named("Demo.Color", true).is_some());
    for member in [
        "X", "Y", "Max", "Point", "Sum", "Describe", "First", "Red", "Blue",
    ] {
        assert!(named(member, false).is_some(), "{member} in {declared:?}");
    }
    // `Sum` is written after the type that declares it, and before the next
    // type: that is the order a member is looked up in.
    let point = declared
        .iter()
        .position(|d| d.name == "Demo.Point")
        .expect("Point");
    let sum = declared.iter().position(|d| d.name == "Sum").expect("Sum");
    assert!(point < sum && declared[point + 1..sum].iter().all(|d| !d.is_type));
}

/// What the printer used to write that C# does not parse — each of them
/// derailed an editor reading the text back for the rest of the file.
#[test]
fn what_it_writes_parses() {
    let source = "using System;\n\
        public class Holder\n\
        {\n\
            public string Name { get; }\n\
            public event Action<int> Changed;\n\
            public Holder(string name) { Name = name; }\n\
            public Holder(int a, int b) : this(((long)a).ToString() + b) { }\n\
            public string Separators() { return \"a\\u2028b\\u2029c\"; }\n\
            public void Fire(int v) { Changed?.Invoke(v); }\n\
            public static bool Allow(Delegate @delegate) { return @delegate.Target == null; }\n\
            public static void Main() { }\n\
        }\n";
    let Some(text) = roundtrip(source, Some("Holder")) else {
        return;
    };
    expect(
        &text,
        &[
            "Name = name;",
            ": this(((long)a).ToString() + b)",
            "\"a\\u2028b\\u2029c\"",
            // Behind `?` the delegate call keeps its name, and the field
            // the event was read from is what it is called on.
            "Changed?.Invoke(v);",
            "@delegate.Target",
        ],
    );
    let tree = parse(SourceText::new("Holder.cs", text.clone()));
    let errors: Vec<String> = tree
        .diagnostics()
        .iter()
        .map(|diagnostic| format!("{diagnostic:?}"))
        .collect();
    assert!(errors.is_empty(), "{errors:#?}\n{text}");
}

/// What both builds of the modern fixture have to read as, in order.
const MODERN_SNIPPETS: &[&str] = &[
    "public record Point(int X, int Y)",
    "public double Length",
    "public class Person(string name, int age)",
    "public int Age { get; } = age;",
    "return $\"{name} ({age})\";",
    "[AttributeUsage(AttributeTargets.Class | AttributeTargets.Field)]",
    "[Tag(\"settings\", Level = 2)]",
    "[Obsolete(\"use Limit\")]",
    "[NonSerialized]",
    "public const decimal Rate = 0.25m;",
    "public required string Title { get; init; }",
    "return (object)a == b;",
    "switch (s)",
    "switch (command)",
    "case \"sub\":\n\t\t\tcase \"minus\":",
    "value = x - 1;",
    "case \"noop\":",
    "Console.WriteLine(\"unknown \" + command);",
    "Console.WriteLine(value);",
    "if (o is int num)",
    "if (o is string text)",
    "return (object)a == b;",
    "return h is null;",
    "return p with { Y = 5 };",
    "return new T();",
    "return a >>> 3;",
    "public static async Task<int> Sum(IAsyncEnumerable<int> xs)",
    "await foreach (int ",
    "public static async Task Finally(Task t)",
    "await t;",
    "finally",
    "await Task.Delay(1);",
    "public static async IAsyncEnumerable<int> Count(int n, CancellationToken ct = default)",
    "for (int i = 0; i < n; i++)",
    "await Task.Delay(1, ct);",
    "yield return i;",
    "public static unsafe int Pointers(int* p, int n, string s)",
    "result += p[i];",
    "fixed (char* ptr = s)",
];

/// Cases, in whatever order each build searches for them.
const MODERN_CASES: &[&str] = &[
    "names.ConvertAll((string n) => new { n, Size = n.Length })",
    "new[] { new { Size = 1 } }",
    "case \"alpha\":\n\t\t\t\treturn 1;",
    "case \"beta\":\n\t\t\t\treturn 2;",
    "case \"gamma\":\n\t\t\t\treturn 3;",
    "case \"eta\":\n\t\t\t\treturn 7;",
    "case \"add\":\n\t\t\t\tvalue = x + 1;\n\t\t\t\tbreak;",
    "_words[i >> 5] |= ",
    "public static readonly int[,] Grid = new int[2, 3] { { 1, 2, 3 }, { 4, 5, 6 } };",
    "ref readonly Holder current = ref Current;",
    "bool Equal<TValue>(List<TValue> x, List<TValue> y)",
    "(string s, out int value) =>",
    "return Total((IEnumerable<int>)xs);",
    "return _kind == Kind.Some;",
    "slot.Size = 4;\n\t\t\t*d = slot;",
    "return 1L << t;",
];

#[test]
fn modern_csharp_from_roslyn_optimized_or_not() {
    let Some(references) = references() else {
        println!("note: skipped; no .NET shared framework was found");
        return;
    };
    let images: Vec<&[u8]> = references.iter().map(Vec::as_slice).collect();
    for fixture in ["roslyn_modern.dll", "roslyn_modern_debug.dll"] {
        let path = format!("{}/tests/fixtures/{fixture}", env!("CARGO_MANIFEST_DIR"));
        let bytes = std::fs::read(path).expect("fixture");
        let text = decompile_with_references(&bytes, &images, None, &Options::default())
            .expect("readable");
        println!("{text}");
        expect(&text, MODERN_SNIPPETS);
        for case in MODERN_CASES {
            assert!(text.contains(case), "{fixture}: no `{case}` in:\n{text}");
        }
        // Nothing of the lowering is left: jumps, state machines, the
        // members a record or a primary constructor has the compiler write.
        for machinery in [
            "goto ",
            "<Clone>$",
            "EqualityContract",
            "<name>P",
            "ComputeStringHash",
            "MoveNext",
            "GetAwaiter",
            "ExceptionDispatchInfo",
            "DisposeAsync",
            "GetPinnableReference",
            "Activator",
            "DecimalConstant",
            "DisplayClass",
        ] {
            assert!(
                !text.contains(machinery),
                "{fixture}: `{machinery}` in:\n{text}"
            );
        }
        let tree = parse(SourceText::new("Modern.cs", text.clone()));
        let errors: Vec<String> = tree
            .diagnostics()
            .iter()
            .map(|diagnostic| format!("{diagnostic:?}"))
            .collect();
        assert!(errors.is_empty(), "{fixture}: {errors:#?}\n{text}");
    }
}
