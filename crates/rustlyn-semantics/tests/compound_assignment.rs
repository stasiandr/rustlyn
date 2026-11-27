//! `x op= y` is `x = x op y` where the result fits `x` (§12.21.4): implicitly,
//! or, for a predefined operator, by a cast that is written for the
//! programmer when `y` converts implicitly to the type of `x` (or the
//! operator is a shift). `byte b; b += 1;` and `short s; s *= 2;` are fine;
//! `int a; a += longValue;` is CS0266. Where no operator takes the operands
//! it is CS0019, or CS0034 where the candidates have no best one.
//!
//! The three tables beside this file were taken from Roslyn: one line per
//! pair of types, and for each of `+= -= *= /= %= &= |= ^= <<= >>= >>>=` the
//! code it reported, or `-` for none.

use std::path::PathBuf;

use rustlyn_semantics::Compilation;
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

const OPERATORS: [&str; 11] = [
    "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", ">>>=",
];

/// The shared framework directory to read assemblies out of, if there is one
/// (`RUSTLYN_FRAMEWORK`, or beside the `dotnet` that `RUSTLYN_DOTNET` or
/// `DOTNET_ROOT` names).
fn framework() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("RUSTLYN_FRAMEWORK") {
        let path = PathBuf::from(path);
        return path.is_dir().then_some(path);
    }
    let root = match std::env::var("RUSTLYN_DOTNET") {
        Ok(path) => PathBuf::from(path).parent()?.to_path_buf(),
        Err(_) => PathBuf::from(std::env::var("DOTNET_ROOT").ok()?),
    };
    let mut versions: Vec<_> = std::fs::read_dir(root.join("shared/Microsoft.NETCore.App"))
        .ok()?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.is_dir())
        .collect();
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

/// The code of every diagnostic a file gets against the real core library,
/// each with the line it is on (from 1); `None` where there is no framework
/// to read, and the tests say so and pass.
fn diagnostics(source: &str) -> Option<Vec<(usize, String)>> {
    let Some(directory) = framework() else {
        eprintln!("no .NET shared framework found; skipping");
        return None;
    };
    let bytes = [
        "System.Private.CoreLib.dll",
        "System.Runtime.dll",
        "System.Console.dll",
        "System.Collections.dll",
    ]
    .iter()
    .filter_map(|name| std::fs::read(directory.join(name)).ok())
    .collect::<Vec<_>>();
    let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
    let tree = parse(SourceText::new("Program.cs", source));
    let compilation = Compilation::create_with_references(vec![tree], &images);
    let mut found: Vec<_> = compilation
        .source_diagnostics()
        .into_iter()
        .map(|entry| entry.diagnostic.clone())
        .chain(
            compilation
                .semantic_diagnostics()
                .into_iter()
                .map(|entry| entry.diagnostic),
        )
        .collect();
    found.sort_by_key(|diagnostic| (diagnostic.span().start(), diagnostic.code()));
    Some(
        found
            .iter()
            .map(|diagnostic| {
                let start: usize = diagnostic.span().start().try_into().expect("an offset");
                let line = source[..start].matches('\n').count() + 1;
                (line, diagnostic.code().to_string())
            })
            .collect(),
    )
}

/// The codes alone, in the order of where they are.
fn codes(source: &str) -> Vec<String> {
    diagnostics(source).map_or_else(
        || vec!["skipped".to_string()],
        |found| found.into_iter().map(|(_, code)| code).collect(),
    )
}

/// Whether the test can run at all.
macro_rules! framework_or_return {
    () => {
        if framework().is_none() {
            eprintln!("no .NET shared framework found; skipping");
            return;
        }
    };
}

/// Runs a table: `left|right|codes` per line. Each row is a method with a
/// line for every operator, built by `statement`, so one compilation answers
/// them all.
fn check_table(table: &str, header: &str, statement: impl Fn(&str, &str) -> String) {
    framework_or_return!();
    let mut source =
        format!("enum E {{ A, B }}\nenum F : byte {{ A = 1, B = 2 }}\nclass C {{\n{header}\n");
    let mut expected_by_line: Vec<(usize, Vec<String>, String)> = Vec::new();
    for (number, line) in table.lines().enumerate() {
        let mut parts = line.split('|');
        let (left, right, expected) = (
            parts.next().expect("left"),
            parts.next().expect("right"),
            parts.next().expect("codes"),
        );
        source.push_str(&format!("void M{number}() {{ {left} a = default;\n"));
        for (operator, expected) in OPERATORS.iter().zip(expected.split(' ')) {
            let line_number = source.matches('\n').count() + 1;
            source.push_str(&statement(operator, right));
            source.push('\n');
            expected_by_line.push((
                line_number,
                expected
                    .split(',')
                    .filter(|code| *code != "-")
                    .map(str::to_string)
                    .collect(),
                format!("{left} {operator} {right}"),
            ));
        }
        source.push_str("}\n");
    }
    source.push('}');
    let found = diagnostics(&source).expect("a framework");
    let mut wrong = Vec::new();
    for (line, expected, what) in expected_by_line {
        let got: Vec<String> = found
            .iter()
            .filter(|(at, _)| *at == line)
            .map(|(_, code)| code.clone())
            .collect();
        if got != expected {
            wrong.push(format!("{what}: expected {expected:?}, got {got:?}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn a_variable_on_the_right_is_judged_as_roslyn_does() {
    check_table(
        include_str!("compound_assignment_variables.txt"),
        "",
        |operator, right| format!("{{ {right} b = default; a {operator} b; }}"),
    );
}

#[test]
fn a_constant_on_the_right_is_judged_as_roslyn_does() {
    check_table(
        include_str!("compound_assignment_constants.txt"),
        "const int K = 5; const byte KB = 5; const long KL = 5; const double KD = 5; \
         const char KC = 'a'; const short KS = 5; const uint KU = 5; const E KE = E.B; \
         const F KF = F.B;",
        |operator, right| format!("a {operator} {right};"),
    );
}

#[test]
fn a_nullable_on_the_left_is_judged_as_roslyn_does() {
    check_table(
        include_str!("compound_assignment_nullables.txt"),
        "",
        |operator, right| format!("{{ {right} b = default; a {operator} b; }}"),
    );
}

#[test]
fn what_roslyn_accepts_is_clean() {
    framework_or_return!();
    let source = r#"
using System;
enum E { A, B }
enum F : byte { A = 1, B = 2 }
struct V { public static V operator +(V a, V b) => a; public static V operator +(V a, int b) => a; }
class P { public byte B { get; set; } public short this[int i] { get => 0; set { } } public event Action Ev; }
unsafe class C {
    byte fb;
    void M(P p, ref byte rb, byte[] arr, Span<byte> span, int* ip, dynamic dy) {
        byte b = 250; b += 10; b -= 1; b *= 2; b /= 2; b %= 100; b &= 0xF; b |= 1; b ^= 3; b <<= 1; b >>= 1; b >>>= 1;
        short s = 1; s += 1; s *= 2; s += b; s += s; s += (short)1; s -= (byte)3;
        char c = 'a'; c += (char)1; c -= 'a'; c <<= 1; c ^= c;
        int i = 0; i += b; i += s; i += c; i += 1; i <<= s; i >>= b; i -= (int)3L;
        uint u = 1; u += 1; u += 1u; u += b; u += c; u <<= 2; u |= 1;
        long l = 1; l += i; l += u; l += 1; l <<= i; l += 3000000000;
        ulong ul = 1; ul += u; ul += 1; ul += b; ul += c; ul <<= 3;
        float f = 1; f += 1; f += i; f += l; f += 1.5f; f += ul;
        double d = 1; d += f; d += i; d += l; d += 1.5; d += ul;
        decimal m = 1; m += 1; m += i; m += l; m += ul; m += 1.5m; m *= u;
        nint ni = 1; ni += 1; ni += i; ni += s; ni += b; ni <<= 2; ni += ni;
        nuint nu = 1; nu += 1; nu += u; nu += b; nu += c; nu <<= i; nu += nu; nu += 1u;
        string str = ""; str += 1; str += 'c'; str += 1.5; str += null; str += E.A; str += true;
        object o = "s"; o += "s";
        bool bo = true; bo &= false; bo |= true; bo ^= bo;
        E e = E.A; e += 1; e -= 1; e |= E.B; e &= E.B; e ^= E.A; e |= 0; e += i; e -= i;
        F ff = F.A; ff += 1; ff |= F.B; ff += b; ff -= (byte)1;
        V v = default; v += v; v += 1;
        p.B += 1; p.B += b; p[0] += 1; p[0] += b; arr[0] += 1; arr[0] <<= 1; rb += 1; rb ^= 1; fb += 1; span[0] += 1;
        checked { b += 10; i += b; fb += 1; }
        ip += 1; ip -= 1; ip += i; ip += l; ip += ul;
        int? n = 1; n += 1; n += b; n <<= 1; n |= 1; n += null; n += n;
        long? nl = 1; nl += n; nl += i; byte? nb = 1; nb += 1; nb += b; nb <<= 1;
        dy += 1; i += dy; b += dy; dy += "s";
        int local = 0; ref int rl = ref local; rl += 1; rl += b;
        i = b += 1;
    }
}
"#;
    assert_eq!(codes(source), Vec::<String>::new());
}

#[test]
fn a_constant_the_small_type_does_not_hold_is_cs0031() {
    framework_or_return!();
    let source = "class C { void M(byte b, sbyte s, short h, ushort us, uint u, char c, long l) {
        b += 300; s += 128; h += 65536; us += -1; u += -1;
        c += 65536; b += 3000000000; b += 1L; l += 3000000000; b <<= 300; } }";
    assert_eq!(
        codes(source),
        [
            "CS0031", "CS0031", "CS0031", "CS0031", "CS0031", "CS0266", "CS0266", "CS0266"
        ]
    );
}

#[test]
fn a_ulong_and_a_signed_number_have_no_best_operator() {
    framework_or_return!();
    let source = "class C { void M(int i, long l, ulong ul, nuint nu, nint ni) {
        i += ul; ul += i; l -= ul; nu += i; nu *= l; ni += nu; } }";
    assert_eq!(codes(source), ["CS0034"; 6]);
}

#[test]
fn a_double_literal_is_cs0664_through_checked_and_in_an_array() {
    framework_or_return!();
    let source = "class C {
        float F1 = checked(1.5);
        decimal F2 = unchecked((1.5));
        float[] F3 = { 1.5 };
        void M() {
            float o = checked(1.5);
            decimal p = unchecked((1.5));
            float[] l = { 1.5 };
            decimal[,] k = { { 1.5 } };
            float[] ok = { 1, 2f, 'c', (float)1.5 };
            double[] fine = { 1.5, 2 };
            float[] sum = { 1.5 + 1 };
        } }";
    assert_eq!(
        codes(source),
        [
            "CS0664", "CS0664", "CS0664", "CS0664", "CS0664", "CS0664", "CS0664", "CS0266"
        ]
    );
}

#[test]
fn an_array_initializer_value_is_assigned_to_the_element() {
    framework_or_return!();
    let source = "using System;
        class B { } class D : B { }
        class C { static void M(string s, long l, dynamic d) {
            int[] a = { 1, 'c', (byte)2, d };
            long[] b = { 1, 2u, 'c' };
            byte[] c = { 1, 255 };
            B[] e = { new D(), null };
            object[] f = { 1, \"s\", null };
            int?[] g = { 1, null };
            Func<int>[] h = { () => 1 };
            int[][] j = { new[] { 1 }, new int[0] };
            int[,] k = { { 1, 2 }, { 3, 4 } };
            var x = new[] { 1, 2L };
            int[] bad1 = { \"s\" };
            int[] bad2 = { l };
            byte[] bad3 = { 256 };
            D[] bad4 = { new B() };
        } }";
    assert_eq!(codes(source), ["CS0029", "CS0266", "CS0031", "CS0266"]);
}

#[test]
fn a_string_joined_to_a_value_is_not_a_constant() {
    framework_or_return!();
    let source = "class K { public const string S = \"s\"; public const int N = 3; }
        class C {
            const string a = K.S + \"x\" + 1;
            const string b = \"a\" + 'c';
            const string c = \"a\" + K.N;
            const int d = \"abc\".Length + 1;
            const char e = \"abc\"[0];
            const string f = $\"{K.S,5}\";
            void M() { const string g = \"a\" + 1.5; const int h = \"abc\".Length; }
        }";
    assert_eq!(codes(source), ["CS0133"; 8]);
}

#[test]
fn what_is_a_constant_stays_one() {
    framework_or_return!();
    let source = "enum E { A }
        class K { public const string S = \"s\"; public const int N = 3; public const decimal M = 2.5m; }
        class C {
            const string a = K.S + \"x\";
            const string b = \"a\" + \"b\" + nameof(C);
            const string c = $\"{K.S}x\";
            const string d = $\"{K.S}x{K.S}\";
            const string e = \"a\" + null;
            const string f = \"a\" + (string)null;
            const string g = \"a\" + (1 > 0 ? \"b\" : \"c\");
            const int h = K.N * 2 + sizeof(int) + (int)E.A;
            const long i = int.MaxValue + 1L;
            const decimal j = K.M * 2 + 1.5m;
            const double k = 1 / 2.0;
            const bool l = \"a\" == \"b\";
            void M() { const string m = K.S + \"y\"; const char n = (char)65; const int o = K.N; }
        }";
    assert_eq!(codes(source), Vec::<String>::new());
}

#[test]
fn a_pattern_value_that_is_no_constant_is_cs9135() {
    framework_or_return!();
    let source = "using System;
        class C {
            static readonly nuint R = 5;
            static nuint F() => 1;
            int P => 1;
            void M(nuint u, int i, int[] a, decimal m, string s, E e) {
                bool b1 = u is R;
                bool b2 = u is > R;
                bool b3 = i is P;
                bool b4 = i is a.Length;
                bool b5 = u is nuint.MaxValue;
                int x = i switch { P => 1, _ => 2 };
                bool ok1 = m is decimal.MaxValue or decimal.Zero or > decimal.MinusOne;
                bool ok2 = u is (nuint)5 or > (nuint)7;
                bool ok3 = i is int.MaxValue or K or < 0;
                bool ok4 = e is E.A;
                bool ok5 = s is null or \"x\" or nameof(C);
                bool ok6 = i is sizeof(int) or (int)E.A;
            }
            const int K = 5;
        }
        enum E { A }";
    assert_eq!(codes(source), ["CS9135"; 6]);
}

#[test]
fn an_operator_an_extension_gives_is_not_overruled() {
    framework_or_return!();
    let source = r"
static class E
{
    extension<T>(T t)
    {
        public static T operator +(T t1, T t2) => throw null!;
    }
}
class C { void M(object o) { o += o; o += 1; } }";
    assert_eq!(codes(source), Vec::<String>::new());
}

#[test]
fn a_value_that_is_only_a_value_is_not_judged_by_its_operator() {
    framework_or_return!();
    let source = r"
struct S { public object P { get => 0; set { } } }
class C { static S Make() => default; void M() { Make().P += 1; } }";
    // Roslyn says CS1612 and nothing about the operator; nothing is said here.
    assert_eq!(codes(source), Vec::<String>::new());
}

#[test]
fn a_const_whose_value_does_not_convert_has_one_error() {
    framework_or_return!();
    let source = r"
class C { }
class D { }
class T { static D F() => null; static void M() { const C d = F(); } }";
    assert_eq!(codes(source), ["CS0029"]);
}
