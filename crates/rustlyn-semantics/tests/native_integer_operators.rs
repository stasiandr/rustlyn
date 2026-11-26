//! `nint` and `nuint` against the other numbers in a binary operator
//! (§12.4.5): the predefined operators both operands reach, and of those the
//! one whose type reaches all the others. `nint` reaches `long`, `float`,
//! `double` and `decimal`; `nuint` reaches `ulong` and those three; neither
//! reaches the other, and a signed type never meets an `nuint` (that leaves
//! only `float`, `double` and `decimal`, which have no best of the three).
//! The expected answers were taken from Roslyn.

use rustlyn_semantics::Compilation;
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

/// The codes of every diagnostic a file gets, in the order of where they are.
fn codes(source: &str) -> Vec<String> {
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
        .collect();
    found.sort_by_key(|diagnostic| (diagnostic.span().start(), diagnostic.code()));
    found
        .iter()
        .map(|diagnostic| diagnostic.code().to_string())
        .collect()
}

/// A body of statements with a variable of every type in scope.
fn in_method(body: &str) -> String {
    format!(
        "class C {{ void M(nint n, nuint u, long l, ulong ul, int i, uint ui, float f, \
         double d, decimal m, short s, char c, nint? nn, nuint? un, long? ln) {{ {body} }} }}"
    )
}

#[test]
fn nint_meets_long_float_double_and_decimal_in_every_comparison() {
    let source = in_method(
        "bool a = l < n; bool b = n > l; bool c1 = f >= n; bool d1 = n <= d; bool e = m < n; \
         bool g = ui > n; bool h = n == ui; bool k = i <= n; bool o = s != n; bool p = c < n;",
    );
    assert_eq!(codes(&source), Vec::<String>::new());
}

#[test]
fn nuint_meets_ulong_float_double_and_decimal_in_every_comparison() {
    let source = in_method(
        "bool a = ul < u; bool b = u > ul; bool c1 = f >= u; bool d1 = u <= d; bool e = m < u; \
         bool g = ui > u; bool h = u == ui; bool k = c <= u;",
    );
    assert_eq!(codes(&source), Vec::<String>::new());
}

#[test]
fn arithmetic_with_a_native_integer_works_in_the_wider_type() {
    let source = in_method(
        "long a = l + n; long b = n * l; long k = n - ui; float e = f / n; double g = u * d; \
         decimal h = m % n; decimal o = u + m; ulong p = u - ul; ulong q = ul * u; \
         long r = ui + n; nuint t = u + ui; nint v = n + s; nint w = c + n;",
    );
    assert_eq!(codes(&source), Vec::<String>::new());
}

#[test]
fn bitwise_operators_take_only_the_integral_types() {
    let source = in_method(
        "long a = n & l; long b = n | ui; ulong c1 = u ^ ul; nint d1 = n & s; nuint e = u | ui;",
    );
    assert_eq!(codes(&source), Vec::<String>::new());
}

#[test]
fn constants_become_the_native_integer() {
    let source = in_method(
        "nint a = n + 1; bool b = n < 5L; bool c1 = u > 0; nuint d1 = u + 1; ulong e = u + 1L; \
         bool g = u == 7L; bool h = 1 < u; bool k = 5L < n; bool o = un > 0; nuint? p = un + 1; \
         bool q = un == 6UL; nint? r = nn + 1;",
    );
    assert_eq!(codes(&source), Vec::<String>::new());
}

#[test]
fn compound_assignment_converts_the_other_side_to_the_variable() {
    let source = in_method(
        "l += n; l *= n; ul += u; f += n; d -= u; m += n; m *= u; n += i; n += s; n <<= 2; \
         u += ui; u += 1; u |= ui; n %= 3;",
    );
    assert_eq!(codes(&source), Vec::<String>::new());
}

#[test]
fn lifted_forms_meet_the_other_numbers_too() {
    let source = in_method(
        "bool a = nn < l; bool b = nn == ln; long? c1 = nn + l; nuint? d1 = un + ui; \
         bool e = un > ul; float? g = nn + f; decimal? h = m + nn; bool k = ln != nn;",
    );
    assert_eq!(codes(&source), Vec::<String>::new());
}

#[test]
fn types_with_no_common_operator_are_errors() {
    // `nint` and `nuint`, `nint` and `ulong`, `nuint` and a signed type:
    // each leaves `float`, `double` and `decimal`, with no best.
    let source = in_method(
        "var a = n + u; var b = n + ul; var c1 = u + l; var d1 = u + i; var e = u - s; \
         bool g = n < ul; bool h = u == l; bool k = n == u;",
    );
    assert_eq!(codes(&source), ["CS0034"; 8]);
}

#[test]
fn bitwise_operators_do_not_reach_floating_point_and_shifts_count_in_int() {
    let source = in_method(
        "var a = n & f; var b = u | d; var c1 = n ^ m; var d1 = n << ui; var e = u >> l; \
         var g = n << n; var h = i << n;",
    );
    assert_eq!(codes(&source), ["CS0019"; 7]);
}

#[test]
fn a_negative_int_constant_is_not_an_nuint() {
    let source = in_method("bool a = u > -1; var b = u + (-1); var c1 = u + i;");
    assert_eq!(codes(&source), ["CS0034"; 3]);
}
