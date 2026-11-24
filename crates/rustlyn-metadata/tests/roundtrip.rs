//! What the emitter writes, the reader has to read back.
//!
//! The two are written from the same specification and from opposite ends, so
//! agreeing is evidence about both. A table whose shape is wrong does not fail
//! loudly — it shifts every table after it and hands back numbers that look
//! like numbers — which is exactly why this compares names and counts rather
//! than merely checking that reading succeeded.

use rustlyn_metadata::{Assembly, table};
use rustlyn_semantics::Compilation;
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

/// Compiles a program and reads its metadata back.
fn build(name: &str, source: &str) -> Vec<u8> {
    let compilation = Compilation::create(vec![parse(SourceText::new("Program.cs", source))]);
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
    assert!(diagnostics.is_empty(), "{name}: {diagnostics:#?}");
    rustlyn_emit::emit(&compilation, name)
        .unwrap_or_else(|error| panic!("{name}: {error}"))
        .assembly
}

/// The full names of the types an assembly declares, `<Module>` aside.
fn type_names(assembly: &Assembly<'_>) -> Vec<String> {
    let heaps = assembly.heaps();
    assembly
        .table(table::TYPE_DEF)
        .iter()
        .map(|row| {
            let namespace = heaps.string(row.number(2));
            let name = heaps.string(row.number(1));
            if namespace.is_empty() {
                name.to_string()
            } else {
                format!("{namespace}.{name}")
            }
        })
        .filter(|name| name != "<Module>")
        .collect()
}

fn method_names(assembly: &Assembly<'_>) -> Vec<String> {
    let heaps = assembly.heaps();
    assembly
        .table(table::METHOD_DEF)
        .iter()
        .map(|row| heaps.string(row.number(3)).to_string())
        .collect()
}

#[test]
fn a_freshly_emitted_assembly_reads_back() {
    let bytes = build(
        "Read",
        r#"
using System;
class Read
{
    static void Main() { Console.WriteLine("hello"); }
}
"#,
    );
    let assembly = Assembly::read(&bytes).expect("the emitter's own output should read");

    assert_eq!(type_names(&assembly), vec!["Read"]);
    assert_eq!(method_names(&assembly), vec!["Main", ".ctor"]);

    // The name and version of the assembly itself.
    let row = assembly
        .table(table::ASSEMBLY)
        .row(1)
        .expect("an assembly row");
    assert_eq!(assembly.heaps().string(row.number(7)), "Read");
    // No `[assembly: AssemblyVersion]`: 0.0.0.0, as csc gives it.
    assert_eq!(row.number(1), 0);

    // The entry point the CLI header names is `Main`, found by token.
    let entry = assembly
        .row(assembly.entry_point)
        .expect("the entry point should name a row");
    assert_eq!(assembly.heaps().string(entry.number(3)), "Main");
}

#[test]
fn every_shape_the_emitter_writes_reads_back() {
    let bytes = build(
        "Shapes",
        r#"
using System;
interface INamed { string Name(); }
enum Colour { Red, Green = 4 }
struct Point { public int X; }
delegate int Op(int x);
record Pair(int A, int B);
class Box<T>
{
    private T item;
    public Box(T item) { this.item = item; }
    public T Item { get { return item; } }
    public class Inner { public int N; }
}
class Shapes : INamed
{
    public const int Limit = 7;
    public string Name() { return "shapes"; }
    static T Echo<T>(T value) { return value; }
    static void Main()
    {
        Console.WriteLine(Echo(Limit) + new Box<int>(1).Item);
        Op f = x => x * 2;
        Console.WriteLine(f(2) + (int)Colour.Green + new Point().X + new Pair(1, 2).A);
        Console.WriteLine(new Shapes().Name() + new Box<int>.Inner().N);
    }
}
"#,
    );
    let assembly = Assembly::read(&bytes).expect("the emitter's own output should read");
    let names = type_names(&assembly);

    // One per declared type, plus the display class a lambda needs.
    for expected in [
        "INamed", "Colour", "Point", "Op", "Pair", "Box`1", "Inner", "Shapes",
    ] {
        assert!(
            names.contains(&expected.to_string()),
            "{expected} in {names:?}"
        );
    }

    // A nested type carries no namespace of its own; `NestedClass` is what
    // says where it sits.
    let nested = assembly.table(table::NESTED_CLASS);
    assert!(!nested.is_empty(), "a nested type should have a row");

    // The pieces the harder features need.
    for (number, what) in [
        (table::GENERIC_PARAM, "a generic parameter"),
        (table::METHOD_SPEC, "a constructed method"),
        (table::TYPE_SPEC, "a constructed type"),
        (table::PROPERTY, "a property"),
        (table::CONSTANT, "a constant"),
        (table::INTERFACE_IMPL, "an implemented interface"),
    ] {
        assert!(assembly.rows(number) > 0, "{what} should have a row");
    }
}

#[test]
fn a_string_literal_reads_back_as_itself() {
    let bytes = build(
        "Literal",
        r#"
using System;
class Literal
{
    static void Main() { Console.WriteLine("привет"); }
}
"#,
    );
    let assembly = Assembly::read(&bytes).expect("the emitter's own output should read");
    // `#US` holds UTF-16, so a literal that needs surrogate pairs or high code
    // points is where a reader that assumed bytes would come apart.
    let text = assembly
        .heaps()
        .user_string(1)
        .expect("the first user string");
    assert_eq!(text, "привет");
}

#[test]
fn something_that_is_not_an_assembly_says_so() {
    assert!(Assembly::read(b"not a PE file at all").is_err());
}

/// The body of the one method called `name`, decoded.
fn body_of(bytes: &[u8], name: &str) -> rustlyn_metadata::Body {
    let assembly = Assembly::read(bytes).expect("the emitter's own output should read");
    let heaps = assembly.heaps();
    let method = assembly
        .table(table::METHOD_DEF)
        .iter()
        .find(|row| heaps.string(row.number(3)) == name)
        .unwrap_or_else(|| panic!("no method called {name}"));
    let offset = assembly
        .image()
        .offset_of(method.number(0))
        .expect("the body should be in a section");
    rustlyn_metadata::Body::read(&assembly.image().bytes()[offset as usize..])
        .expect("the body should decode")
}

#[test]
fn the_il_the_emitter_wrote_decodes_back() {
    let bytes = build(
        "Body",
        r#"
using System;
class Body
{
    static int Twice(int x) { return x + x; }
    static void Main() { Console.WriteLine(Twice(21)); }
}
"#,
    );
    let body = body_of(&bytes, "Twice");
    let names: Vec<&str> = body
        .instructions
        .iter()
        .map(|instruction| instruction.name)
        .collect();
    assert_eq!(names, vec!["ldarg.0", "ldarg.0", "add", "ret"]);

    // Offsets are where the emitter put them, so the last one plus its width
    // is the size the header declared.
    let last = body.instructions.last().expect("an instruction");
    assert_eq!(last.offset + last.width(), body.code_size);
}

#[test]
fn a_branch_decodes_to_where_it_goes() {
    let bytes = build(
        "Branch",
        r#"
using System;
class Branch
{
    static int Sum(int n)
    {
        int total = 0;
        for (int i = 0; i < n; i++) { total += i; }
        return total;
    }
    static void Main() { Console.WriteLine(Sum(4)); }
}
"#,
    );
    let body = body_of(&bytes, "Sum");
    // Every branch has to land on the start of an instruction; one that does
    // not means an operand width is wrong somewhere.
    let starts: Vec<u32> = body
        .instructions
        .iter()
        .map(|instruction| instruction.offset)
        .collect();
    let mut branches = 0;
    for instruction in &body.instructions {
        if let rustlyn_metadata::body::Value::Target(at) = instruction.value {
            branches += 1;
            assert!(
                starts.contains(&at) || at == body.code_size,
                "{} at IL_{:04x} goes to IL_{at:04x}, which is not an instruction",
                instruction.name,
                instruction.offset
            );
        }
    }
    assert!(branches >= 2, "a loop should have at least two branches");
}

#[test]
fn exception_regions_read_back() {
    let bytes = build(
        "Guarded",
        r#"
using System;
class Guarded
{
    static void Main()
    {
        try { throw new ArgumentException("bad"); }
        catch (ArgumentException e) { Console.WriteLine(e.Message); }
        finally { Console.WriteLine("done"); }
    }
}
"#,
    );
    let body = body_of(&bytes, "Main");
    assert_eq!(body.regions.len(), 2, "a catch and a finally");
    assert!(matches!(
        body.regions[0].kind,
        rustlyn_metadata::body::Handler::Catch(_)
    ));
    assert!(matches!(
        body.regions[1].kind,
        rustlyn_metadata::body::Handler::Finally
    ));
    // The `finally` guards the `catch` as well, so its region is the wider one.
    assert!(body.regions[1].try_length > body.regions[0].try_length);
}

#[test]
fn a_string_literal_in_the_il_points_back_at_its_text() {
    let bytes = build(
        "Says",
        r#"
using System;
class Says
{
    static void Main() { Console.WriteLine("spoken"); }
}
"#,
    );
    let assembly = Assembly::read(&bytes).expect("the emitter's own output should read");
    let body = body_of(&bytes, "Main");
    let load = body
        .instructions
        .iter()
        .find(|instruction| instruction.name == "ldstr")
        .expect("a string literal");
    let rustlyn_metadata::body::Value::Token(token) = load.value else {
        panic!("`ldstr` carries a token");
    };
    // A `ldstr` token is an offset into `#US` rather than a row in any table.
    assert_eq!(token.table(), 0x70);
    assert_eq!(
        assembly.heaps().user_string(token.row()).as_deref(),
        Ok("spoken")
    );
}

/// The signature blob of the one method called `name`, parsed.
fn signature_of(bytes: &[u8], name: &str) -> rustlyn_metadata::MethodSig {
    let assembly = Assembly::read(bytes).expect("the emitter's own output should read");
    let heaps = assembly.heaps();
    let method = assembly
        .table(table::METHOD_DEF)
        .iter()
        .find(|row| heaps.string(row.number(3)) == name)
        .unwrap_or_else(|| panic!("no method called {name}"));
    let blob = heaps.blob(method.number(4)).expect("a signature blob");
    rustlyn_metadata::Blob::new(blob)
        .method_sig()
        .expect("the signature should parse")
}

#[test]
fn the_signatures_the_emitter_wrote_parse_back() {
    use rustlyn_metadata::TypeSig;

    let bytes = build(
        "Sigs",
        r#"
using System;
using System.Collections.Generic;
class Box<T> { public T Item; }
class Sigs
{
    static void Plain(int a, string b) { }
    static T Echo<T>(T value) { return value; }
    static int[] Array(List<string> items) { return null; }
    static void Out(out int half) { half = 0; }
    int Instance() { return 0; }
    static Box<int> Constructed() { return null; }
    static void Main() { }
}
"#,
    );

    let plain = signature_of(&bytes, "Plain");
    assert!(!plain.instance);
    assert_eq!(plain.returns, TypeSig::Void);
    assert_eq!(plain.parameters, vec![TypeSig::Int32, TypeSig::String]);

    // A generic method says its own arity, and names its parameter by
    // position rather than by name.
    let echo = signature_of(&bytes, "Echo");
    assert_eq!(echo.arity, 1);
    assert_eq!(echo.returns, TypeSig::MVar(0));
    assert_eq!(echo.parameters, vec![TypeSig::MVar(0)]);

    let array = signature_of(&bytes, "Array");
    assert_eq!(array.returns, TypeSig::Vector(Box::new(TypeSig::Int32)));
    assert!(
        matches!(&array.parameters[0], TypeSig::Generic { arguments, .. }
            if arguments == &[TypeSig::String]),
        "{:?}",
        array.parameters[0]
    );

    // `out` is a reference, which is all the runtime sees of it.
    let out = signature_of(&bytes, "Out");
    assert_eq!(
        out.parameters,
        vec![TypeSig::ByRef(Box::new(TypeSig::Int32))]
    );

    assert!(signature_of(&bytes, "Instance").instance);

    let constructed = signature_of(&bytes, "Constructed");
    assert!(
        matches!(&constructed.returns, TypeSig::Generic { arguments, .. }
            if arguments == &[TypeSig::Int32]),
        "{:?}",
        constructed.returns
    );
}
