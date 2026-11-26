//! Constants that do not fit the type they are given: an enumerator past the
//! last value of its underlying type (CS0543), and an `int` constant that
//! does not fit a smaller integral type (CS0031, where CS0266 would be
//! reported for any other value). Each look-alike that Roslyn accepts is
//! here too, and must stay quiet.

use rustlyn_semantics::Compilation;
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

/// Every diagnostic for a file, as `CS0000 'underlined': message`, in the
/// order of where they are.
fn diagnose(source: &str) -> Vec<String> {
    let compilation = Compilation::create(vec![parse(SourceText::new("Program.cs", source))]);
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
        .filter(|diagnostic| diagnostic.is_error())
        .collect();
    found.sort_by_key(|diagnostic| (diagnostic.span().start(), diagnostic.code()));
    found
        .iter()
        .map(|diagnostic| {
            let span = diagnostic.span();
            format!(
                "{} '{}': {}",
                diagnostic.code(),
                &source[span.start() as usize..span.end() as usize],
                diagnostic.message()
            )
        })
        .collect()
}

/// Just the codes.
fn codes(source: &str) -> Vec<String> {
    diagnose(source)
        .into_iter()
        .map(|line| line[..6].to_string())
        .collect()
}

/// A statement list inside a method of a class.
fn in_method(body: &str) -> String {
    format!("class C {{ void M() {{ {body} }} }}")
}

#[test]
fn an_enumerator_past_the_last_value_of_its_type_is_cs0543() {
    assert_eq!(
        diagnose("enum EB : byte { X = 255, Y }"),
        ["CS0543 'Y': 'EB.Y': the enumerator value is too large to fit in its type"]
    );
    // Only the first overflowing member of a run is reported.
    assert_eq!(
        diagnose("enum EB : byte { X = 255, Y, Z }"),
        ["CS0543 'Y': 'EB.Y': the enumerator value is too large to fit in its type"]
    );
    // Each of the integral types has its own last value.
    assert_eq!(codes("enum E1 : sbyte { X = 127, Y }"), ["CS0543"]);
    assert_eq!(codes("enum E2 : short { X = 32767, Y }"), ["CS0543"]);
    assert_eq!(codes("enum E3 : ushort { X = 65535, Y }"), ["CS0543"]);
    assert_eq!(codes("enum E4 { A = 2147483647, B }"), ["CS0543"]);
    assert_eq!(codes("enum E5 : int { A = 2147483647, B }"), ["CS0543"]);
    assert_eq!(codes("enum E6 : uint { X = 4294967295, Y }"), ["CS0543"]);
    assert_eq!(
        codes("enum E7 : long { X = 9223372036854775807, Y }"),
        ["CS0543"]
    );
    assert_eq!(
        codes("enum E8 : ulong { X = 18446744073709551615, Y }"),
        ["CS0543"]
    );
    // The member after an overflow has no value to count from, so a later
    // run is quiet until a member gives a value of its own.
    assert_eq!(codes("enum E9 : byte { X = 255, Y, Z = 0, W }"), ["CS0543"]);
    // Counting from a member given a value of its own.
    assert_eq!(codes("enum E10 : byte { X = 254, Y, Z }"), ["CS0543"]);
    assert_eq!(codes("enum E11 : byte { X = 255, Y = X, Z }"), ["CS0543"]);
    assert_eq!(codes("enum E12 : byte { X = 255, Y = 255, Z }"), ["CS0543"]);
    assert_eq!(codes("enum E13 { A = 2147483646, B, C }"), ["CS0543"]);
    assert_eq!(codes("enum E14 : byte { X = 200 + 55, Y }"), ["CS0543"]);
}

#[test]
fn an_enumerator_that_fits_is_not_cs0543() {
    let fine = [
        // Given a value of its own at the maximum.
        "enum E : byte { X = 255 }",
        "enum E : byte { X = 255, Y = 0 }",
        "enum E : byte { X = 255, Y = 1, Z }",
        "enum E : byte { A = 255, B = 0, C, D = 1, E }",
        "enum E : byte { X = 255, Y = 255 }",
        "enum E : sbyte { X = 127 }",
        "enum E : sbyte { X = -128, Y, Z = 127 }",
        "enum E : short { X = 32767, Y = -32768, Z }",
        "enum E : ushort { X = 65534, Y }",
        "enum E : ushort { X = 65535 }",
        "enum E : int { X = 2147483646, Y }",
        "enum E : uint { X = 1u << 31, Y, Z = 4294967294, W }",
        "enum E : uint { X = 4294967294, Y }",
        // A `ulong` past `long.MaxValue` is still a value that is not the
        // maximum, and `long.MaxValue` followed by one is fine as `ulong`.
        "enum E : ulong { X = 9223372036854775807, Y, Z }",
        "enum E : ulong { X = 18446744073709551614, Y }",
        "enum E : long { X = 9223372036854775806, Y }",
        // Flags enums, written with values.
        "enum F : byte { A = 128, B = 64, C = 32, D = 1 }",
        "enum F : byte { A = 1, B = 2, C = 128, D = 0 }",
        // Enums of `int` that do not reach the end.
        "enum E { A = 2147483646, B }",
        "enum E { A, B = 2147483647 }",
    ];
    for source in fine {
        assert!(
            codes(source).is_empty(),
            "expected nothing for {source}, found {:#?}",
            diagnose(source)
        );
    }
}

#[test]
fn a_constant_too_big_for_a_smaller_integer_is_cs0031() {
    assert_eq!(
        diagnose(&in_method("byte b = 300;")),
        ["CS0031 '300': Constant value '300' cannot be converted to a 'byte'"]
    );
    assert_eq!(
        diagnose(&in_method("sbyte s = 200;")),
        ["CS0031 '200': Constant value '200' cannot be converted to a 'sbyte'"]
    );
    assert_eq!(
        diagnose(&in_method("ushort u = -1;")),
        ["CS0031 '-1': Constant value '-1' cannot be converted to a 'ushort'"]
    );
    assert_eq!(
        diagnose(&in_method("uint x = -1;")),
        ["CS0031 '-1': Constant value '-1' cannot be converted to a 'uint'"]
    );
    assert_eq!(
        diagnose(&in_method("ulong x = -1;")),
        ["CS0031 '-1': Constant value '-1' cannot be converted to a 'ulong'"]
    );
    assert_eq!(
        diagnose(&in_method("short s = 40000;")),
        ["CS0031 '40000': Constant value '40000' cannot be converted to a 'short'"]
    );
    assert_eq!(
        diagnose(&in_method("ushort u = 70000;")),
        ["CS0031 '70000': Constant value '70000' cannot be converted to a 'ushort'"]
    );
    // A value worked out at compile time, and a constant named.
    assert_eq!(
        diagnose(&in_method("byte b = 200 + 100;")),
        ["CS0031 '200 + 100': Constant value '300' cannot be converted to a 'byte'"]
    );
    assert_eq!(
        diagnose(&in_method("const byte B = 200 + 100;")),
        ["CS0031 '200 + 100': Constant value '300' cannot be converted to a 'byte'"]
    );
    assert_eq!(
        diagnose(&in_method("const int K = 300; byte b = K;")),
        ["CS0031 'K': Constant value '300' cannot be converted to a 'byte'"]
    );
    assert_eq!(
        diagnose(&in_method("byte b = 'a' + 200;")),
        ["CS0031 ''a' + 200': Constant value '297' cannot be converted to a 'byte'"]
    );
    assert_eq!(
        diagnose("class C { byte R() { return 300; } }"),
        ["CS0031 '300': Constant value '300' cannot be converted to a 'byte'"]
    );
}

#[test]
fn a_constant_of_another_type_or_a_value_not_known_is_still_cs0266() {
    // The `int` constant is the only one that is CS0031: a `uint`, a `long`,
    // a `char` or a `double` is CS0266, and so is a value not known until
    // it runs, and a target that is not an integer type.
    for body in [
        "int i = 3000000000;",
        "int i = 5L;",
        "int i = 1L << 40;",
        "char c = 65;",
        "byte b = 'a';",
        "byte b = 300u;",
        "ushort u = 70000u;",
        "const double D = 300; byte b = D;",
        "int x = 300; byte b = x;",
        "byte? nb = 300;",
    ] {
        let source = in_method(body);
        let found = codes(&source);
        assert!(
            found.iter().all(|code| code != "CS0031"),
            "expected no CS0031 for {body}, found {:#?}",
            diagnose(&source)
        );
    }
    assert_eq!(codes(&in_method("int x = 300; byte b = x;")), ["CS0266"]);
}

#[test]
fn a_constant_that_fits_or_is_explicit_is_quiet() {
    for body in [
        "byte b = 255; sbyte s = -128; ushort u = 65535;",
        "uint x = 4294967295; ulong ul = 5; long l = 300;",
        "byte b = 200 + 55; byte c = 1 + 2; short s = 32767;",
        "byte b = unchecked((byte)300);",
        "uint x = unchecked((uint)-1);",
        "int i = 2147483647; long l = 9223372036854775807;",
        "ulong ul = 18446744073709551615;",
    ] {
        assert!(
            diagnose(&in_method(body)).is_empty(),
            "expected nothing for {body}, found {:#?}",
            diagnose(&in_method(body))
        );
    }
    // A method argument is CS1503, not CS0031.
    assert_eq!(
        codes("class C { static void Use(byte value) { } void M() { Use(300); } }"),
        ["CS1503"]
    );
}

#[test]
fn a_constant_that_failed_to_fold_is_the_only_error() {
    // Roslyn gives the division or the overflow and no more: what has no
    // value is not converted to anything.
    for body in [
        "byte a = 3 / 0;",
        "byte a = 3 % 0;",
        "byte a = (3 / 0);",
        "byte a = 1 + 3 / 0;",
        "short a = 3 / 0 + 1;",
        "uint a = 3 / 0;",
        "char a = 3 / 0;",
        "string a = 3 / 0;",
        "byte a = unchecked(3 / 0);",
    ] {
        assert_eq!(codes(&in_method(body)), ["CS0020"], "for {body}");
    }
    for body in [
        "byte a = 2147483647 + 1;",
        "byte a = -(-2147483647 - 1);",
        "byte a = checked(2147483647 + 1);",
        "sbyte a = (2147483647 * 2);",
    ] {
        assert_eq!(codes(&in_method(body)), ["CS0220"], "for {body}");
    }
    assert_eq!(
        codes("class C { static byte R() { return 3 / 0; } byte f = 3 / 0; }"),
        ["CS0020", "CS0020"]
    );
}

#[test]
fn an_out_of_range_constant_is_reported_inside_its_parentheses_and_checked() {
    // The error is about the value, which is what is inside the wrappers.
    assert_eq!(
        diagnose(&in_method("byte p = unchecked(256);")),
        ["CS0031 '256': Constant value '256' cannot be converted to a 'byte'"]
    );
    for body in [
        "byte p = checked(256);",
        "byte p = (256);",
        "byte p = ((256));",
        "byte p = unchecked((256));",
        "byte p = (unchecked(256));",
        "byte p = checked(unchecked(256));",
    ] {
        assert_eq!(
            diagnose(&in_method(body)),
            ["CS0031 '256': Constant value '256' cannot be converted to a 'byte'"],
            "for {body}"
        );
    }
    assert_eq!(
        diagnose(&in_method("byte p = unchecked(1 + 256);")),
        ["CS0031 '1 + 256': Constant value '257' cannot be converted to a 'byte'"]
    );
    assert_eq!(
        diagnose(&in_method("byte p = unchecked(2147483647 + 1);")),
        ["CS0031 '2147483647 + 1': Constant value '-2147483648' cannot be converted to a 'byte'"]
    );
    assert_eq!(
        diagnose(&in_method("int x = 1; byte p = (x);")),
        [
            "CS0266 'x': Cannot implicitly convert type 'int' to 'byte'. An explicit conversion exists (are you missing a cast?)"
        ]
    );
    assert_eq!(
        diagnose("class C { static byte R() { return unchecked(256); } byte f = (257); }"),
        [
            "CS0031 '256': Constant value '256' cannot be converted to a 'byte'",
            "CS0031 '257': Constant value '257' cannot be converted to a 'byte'",
        ]
    );
}

#[test]
fn a_float_constant_at_the_top_of_a_range_is_out_of_it() {
    // `9223372036854775807` is no `double`: the one that stands for it is 2^63.
    for body in [
        "const long L = (long)(float)9223372036854775807;",
        "const long L = (long)(double)9223372036854775807;",
        "const ulong L = (ulong)(float)18446744073709551615;",
        "const int L = (int)(float)2147483647;",
        "const uint L = (uint)(float)4294967295;",
    ] {
        assert_eq!(codes(&in_method(body)), ["CS0221"], "for {body}");
    }
    for body in [
        "const int L = (int)(double)2147483647;",
        "const long L = (long)(float)(9223372036854775807 / 2);",
        "const long L = unchecked((long)(float)9223372036854775807);",
        "const int L = (int)2147483647.5;",
        "const long L = (long)-9.223372036854775808E18;",
    ] {
        assert!(diagnose(&in_method(body)).is_empty(), "for {body}");
    }
}
