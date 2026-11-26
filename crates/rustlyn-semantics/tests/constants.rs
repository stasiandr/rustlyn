//! Constant values of enum members, where one is written in terms of another.
//!
//! These once recursed without end — binding a member's initializer folds
//! the members it names, and valuing a member walked every member before
//! it — and took the editor down with them, on a flags enum as ordinary as
//! `All = A | B` written ahead of `A` and `B`.

use rustlyn_semantics::{Binder, Compilation, SymbolId};
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

fn compile(source: &str) -> Compilation {
    Compilation::create(vec![parse(SourceText::new("File0.cs", source))])
}

fn find(compilation: &Compilation, path: &str) -> SymbolId {
    compilation
        .symbols()
        .iter()
        .find(|symbol| compilation.symbols().qualified_name(symbol.id) == path)
        .unwrap_or_else(|| panic!("no symbol named {path}"))
        .id
}

/// The value of the constant at `path`, as the debugger would print it.
fn value(compilation: &Compilation, path: &str) -> Option<String> {
    Binder::new(compilation)
        .constant_value(find(compilation, path))
        .map(|value| format!("{value:?}"))
}

#[test]
fn a_member_written_ahead_of_the_members_it_names_has_their_value() {
    let compilation = compile("enum Flags { All = A | B, A = 1, B = 2, C }");
    // Each asked first, in its own compilation: the cache must not be what
    // makes the answer come out.
    for (path, digit) in [
        ("Flags.A", "1"),
        ("Flags.B", "2"),
        ("Flags.All", "3"),
        ("Flags.C", "3"),
    ] {
        let compilation = compile("enum Flags { All = A | B, A = 1, B = 2, C }");
        let found = value(&compilation, path).unwrap_or_else(|| panic!("{path} has no value"));
        assert!(found.contains(digit), "{path} is {found}, not {digit}");
    }
    assert!(value(&compilation, "Flags.All").is_some());
}

#[test]
fn members_defined_in_terms_of_each_other_have_no_value_rather_than_no_end() {
    let compilation = compile("enum Loop { A = B, B = A, C }");
    assert_eq!(value(&compilation, "Loop.A"), None);
    assert_eq!(value(&compilation, "Loop.B"), None);
    let compilation = compile("enum Self { A = A + 1 }");
    assert_eq!(value(&compilation, "Self.A"), None);
}

/// The constants of `source`, each asked in a compilation of its own.
fn values(source: &str, paths: &[&str]) -> Vec<String> {
    paths
        .iter()
        .map(|path| {
            let compilation = compile(source);
            value(&compilation, path).unwrap_or_else(|| format!("{path} has no value"))
        })
        .collect()
}

#[test]
fn a_floating_constant_cast_to_an_integer_is_cut_off_toward_zero() {
    // The cast was dropped and the `3.7` kept: `(int)3.7 + 0.5` came to 4.2,
    // and `const int n = (int)3.7;` was a `double` where an `int` is loaded.
    let source = "class C {
        const int Up = (int)3.7;
        const int Down = (int)-3.7;
        const long Wide = (long)1e10;
        const byte Narrow = (byte)3.99f;
        const char Letter = (char)65.7;
        const double Sum = (int)3.7 + 0.5;
        const double Twice = (double)(int)2.9 * 2;
        const int Half = (int)3.7 / 2;
        const ulong Huge = (ulong)1.8e19;
    }";
    assert_eq!(
        values(
            source,
            &[
                "C.Up", "C.Down", "C.Wide", "C.Narrow", "C.Letter", "C.Sum", "C.Twice", "C.Half",
                "C.Huge"
            ]
        ),
        [
            "Int32(3)",
            "Int32(-3)",
            "Int64(10000000000)",
            "Int32(3)",
            "Char('A')",
            "Double(3.5)",
            "Double(4.0)",
            "Int32(1)",
            "UInt64(18000000000000000000)",
        ]
    );
}

#[test]
fn a_double_cast_to_a_float_is_the_float() {
    // `(float)0.1` is `0.1f`, which is not the `double` 0.1.
    let source = "class C {
        const float Tenth = (float)0.1;
        const bool Same = (float)0.1 == 0.1f;
        const bool Wider = (double)0.1f == 0.1;
    }";
    assert_eq!(
        values(source, &["C.Tenth", "C.Same", "C.Wider"]),
        ["Single(0.1)", "Boolean(true)", "Boolean(false)"]
    );
}

#[test]
fn an_enum_over_ulong_goes_past_long_max() {
    // A member past `long.MaxValue` had no value at all, and the enum did
    // not compile: the value was kept as a `long`.
    let source = "enum Bits : ulong {
        Top = 1UL << 63,
        After,
        Max = 0xFFFFFFFFFFFFFFFF,
        Mix = Top | 1,
        Inverse = ~1UL,
        Less = Max - 1,
    }";
    assert_eq!(
        values(
            source,
            &[
                "Bits.Top",
                "Bits.After",
                "Bits.Max",
                "Bits.Mix",
                "Bits.Inverse",
                "Bits.Less"
            ]
        ),
        [
            "UInt64(9223372036854775808)",
            "UInt64(9223372036854775809)",
            "UInt64(18446744073709551615)",
            "UInt64(9223372036854775809)",
            "UInt64(18446744073709551614)",
            "UInt64(18446744073709551614)",
        ]
    );
}

#[test]
fn integer_constants_fold_as_the_numbers_they_are() {
    // In the type the operator works in: a `ulong` past `long.MaxValue` is
    // arithmetic like any other, `unchecked` wraps at the type's own width,
    // and `>>>` shifts the bits the type has.
    let source = "class C {
        const ulong Big = 0xFFFFFFFFFFFFFFFF;
        const ulong Half = Big / 2 + 1;
        const bool More = Big > 5;
        const int Wrapped = unchecked(2147483647 + 1);
        const uint Under = unchecked(0u - 1);
        const long Product = unchecked(9223372036854775807 * 2);
        const int Logical = -1 >>> 28;
        const long LogicalWide = -1L >>> 60;
        const int Shifted = 1 << 33;
        const long ShiftedWide = 1L << 65;
        const int Remainder = unchecked(-2147483647 - 1) % -1;
        const int Hash = unchecked((int)2166136261 * 16777619);
    }";
    assert_eq!(
        values(
            source,
            &[
                "C.Half",
                "C.More",
                "C.Wrapped",
                "C.Under",
                "C.Product",
                "C.Logical",
                "C.LogicalWide",
                "C.Shifted",
                "C.ShiftedWide",
                "C.Remainder",
                "C.Hash"
            ]
        ),
        [
            "UInt64(9223372036854775808)",
            "Boolean(true)",
            "Int32(-2147483648)",
            "UInt32(4294967295)",
            "Int64(-2)",
            "Int32(15)",
            "Int64(15)",
            "Int32(2)",
            "Int64(2)",
            "Int32(0)",
            "Int32(84696351)",
        ]
    );
}

#[test]
fn an_integer_cast_to_a_float_type_is_the_nearest_number_it_has() {
    // Left as the integer it was written as, `(int)(float)16777217` came
    // back as 16777217, and `(long)(float)9223372036854775807` as 0.
    let source = "class C {
        const int A = (int)(float)16777217;
        const long B = (long)(float)123456789;
        const double E = (float)16777217 + 0.0;
        const double F = (double)(float)123456789;
        const long G = unchecked((long)(float)9223372036854775807);
        const int H = unchecked((int)(float)2147483647);
        const float I = 16777217;
        const float J = 18446744073709551615;
        const double K = 18446744073709551615;
        const float L = 16777217L + 1f;
        const double M = (double)(9223372036854775807 - 1);
        const double N = (float)'a' / 3;
        const bool Same = (float)0.1 == 0.1;
        const double Mixed = 0.1f + 0.2;
        const float Summed = 16777216f + 1 + 1;
    }";
    assert_eq!(
        values(
            source,
            &[
                "C.A", "C.B", "C.E", "C.F", "C.G", "C.H", "C.I", "C.J", "C.K", "C.L", "C.M", "C.N",
                "C.Same", "C.Mixed", "C.Summed"
            ]
        ),
        [
            "Int32(16777216)",
            "Int64(123456792)",
            "Double(16777216.0)",
            "Double(123456792.0)",
            "Int64(0)",
            "Int32(0)",
            "Single(16777216.0)",
            "Single(1.8446744e19)",
            "Double(1.8446744073709552e19)",
            "Single(16777216.0)",
            "Double(9.223372036854776e18)",
            "Double(32.33333206176758)",
            "Boolean(false)",
            "Double(0.30000000149011613)",
            "Single(16777216.0)",
        ]
    );
}

#[test]
fn a_chain_of_thousands_of_constants_binds_in_linear_time() {
    // Every operator asked its operands for their value, and each of those
    // worked it out from the first term again: 4,000 terms took half a
    // minute. Whatever the machine, a few seconds is far from that.
    let ones = "+1".repeat(3000);
    let strings = "+\"a\"".repeat(3000);
    let source = format!(
        "class C {{
            const int Sum = 1{ones};
            const string Text = \"a\"{strings};
            static int Plain(int x) => 1{ones} + x;
            static int Left(int x) => x{ones};
        }}"
    );
    // A chain this long is as deep as the parser goes, which a test thread's
    // stack is not.
    rustlyn_semantics::parallel::deep(|| {
        let started = std::time::Instant::now();
        let compilation = compile(&source);
        assert_eq!(value(&compilation, "C.Sum").as_deref(), Some("Int32(3001)"));
        let text = value(&compilation, "C.Text").expect("a constant string");
        assert_eq!(text.len(), "String(\"\")".len() + 3001);
        assert!(compilation.semantic_diagnostics().is_empty());
        assert!(
            started.elapsed() < std::time::Duration::from_secs(20),
            "binding took {:?}",
            started.elapsed()
        );
    });
}

/// The codes of the errors a file has, in the order of where they are.
fn error_codes(source: &str) -> Vec<String> {
    let compilation = compile(source);
    let mut found: Vec<_> = compilation
        .semantic_diagnostics()
        .into_iter()
        .map(|entry| entry.diagnostic)
        .filter(|diagnostic| diagnostic.is_error())
        .collect();
    found.sort_by_key(|diagnostic| diagnostic.span().start());
    found
        .iter()
        .map(|diagnostic| diagnostic.code().to_string())
        .collect()
}

#[test]
fn a_constant_out_of_the_range_of_its_type_is_the_values_error() {
    assert_eq!(
        error_codes(
            "class C { void M() {
                ulong a = -1L;
                ulong b = (long)-1;
                const long cl = -5;
                ulong c = cl;
                ulong fine = 5L;
                uint d = -1L;
                float e = 1e40;
                float f = (1.5);
                decimal g = 1.5;
                decimal h = 5d;
                float i = -1.5;
                float j = 1.5 + 1;
            } }"
        ),
        [
            "CS0031", "CS0031", "CS0031", "CS0266", "CS0664", "CS0664", "CS0664", "CS0664",
            "CS0266", "CS0266"
        ]
    );
}
