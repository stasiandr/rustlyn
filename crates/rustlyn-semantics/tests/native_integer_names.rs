//! `nint` and `nuint` as the left of a member access (`nint.MaxValue`):
//! they are contextual keywords, so a type, local or namespace of that name
//! in scope answers instead, and `@nint` is never the keyword. The core
//! library these tests bind against is a synthesised one without the members
//! of `IntPtr`, so what is asked here is that the name is found (no CS0103).

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

#[test]
fn static_members_are_reached_through_nint_and_nuint() {
    let source = r#"
class C
{
    unsafe void M()
    {
        nint a = nint.MaxValue;
        nint b = nint.MinValue;
        nuint c = nuint.MaxValue;
        nuint d = nuint.MinValue;
        int e = nint.Size + nuint.Size;
        nint f = nint.Zero;
        nint g = nint.Parse("1");
        string h = nint.MaxValue.ToString();
        nint i = (nint)1 + nint.Size;
        string j = nameof(nint.MaxValue);
        var k = typeof(nint);
        nint l = default(nint);
        int m = sizeof(nint);
    }
}
"#;
    assert!(!codes(source).contains(&"CS0103".to_string()));
}

#[test]
fn a_type_local_or_field_named_nint_answers_first() {
    let source = r#"
class nint { public static int MaxValue; }
class C
{
    static int nuint;
    void M()
    {
        int a = nint.MaxValue;
        int b = nuint;
        var nint = new { MaxValue = 1 };
        int c = nint.MaxValue;
    }
}
"#;
    assert_eq!(codes(source), Vec::<String>::new());
}

#[test]
fn a_verbatim_name_is_not_the_keyword() {
    let source = "class C { void M() { var a = @nint.MaxValue; var b = nint.Bogus; } }";
    assert_eq!(codes(source), ["CS0103", "CS0117"]);
}
