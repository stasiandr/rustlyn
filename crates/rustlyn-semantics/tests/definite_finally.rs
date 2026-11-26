//! Definite assignment across a `finally`: a `break`, a `continue`, a
//! `return` or a `goto` out of a `try` runs the `finally` on its way, so it
//! arrives with what the `finally` assigns as well. Each body here was
//! judged by the real compiler first.

use rustlyn_semantics::Compilation;
use rustlyn_syntax::parse;
use rustlyn_text::SourceText;

/// Every diagnostic for a file, as `CS0000`.
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

/// Just the codes of definite assignment.
fn only(source: &str, wanted: &[&str]) -> Vec<String> {
    codes(source)
        .into_iter()
        .filter(|code| wanted.contains(&code.as_str()))
        .collect()
}

/// A method returning `int`, with a `bool c` to branch on, a `Use(int)` to
/// read with and a `Cond()`.
fn method(body: &str) -> String {
    format!(
        "using System;
        class C {{
            static void Use(int x) {{ }}
            static bool Cond() => true;
            int M(bool c) {{ {body} }}
        }}"
    )
}

/// A method with an `out int r` and a `bool c`.
fn with_out(body: &str) -> String {
    format!(
        "using System;
        class C {{
            static void Use(int x) {{ }}
            static bool Cond() => true;
            void M(out int r, bool c) {{ {body} }}
        }}"
    )
}

#[test]
fn a_jump_out_of_a_try_that_the_finally_does_not_cover_is_cs0165() {
    for body in [
        // `return` out of the body and out of a catch.
        "int x; try { if (c) return 1; } finally { } return x;",
        "int x; try { if (c) return 1; } finally { if (c) x = 2; } return x;",
        "int x; try { if (c) return x; } finally { x = 2; } return 0;",
        "int x; try { try { if (c) return 1; } finally { } } finally { } return x;",
        "int x; try { } catch { if (c) return 1; x = 1; } finally { } return x;",
        "int x; try { } catch { return 1; } finally { } return x;",
        // `break` and `continue`.
        "int x; while (true) { try { if (Cond()) break; } finally { } } Use(x); return 0;",
        "int x; while (true) { try { if (Cond()) break; } finally { if (Cond()) x = 1; } } Use(x); return 0;",
        "int x; while (c) { try { if (Cond()) break; } finally { x = 1; } } Use(x); return 0;",
        "int x; while (true) { try { while (true) { break; } } finally { } break; } Use(x); return 0;",
        "int x; int i = 0; while (i++ < 3) { try { if (Cond()) continue; } finally { } Use(x); } return 0;",
        "int x; do { try { if (Cond()) continue; } finally { } } while (x > 0); return 0;",
        "for (;;) { int x; try { try { if (Cond()) break; } finally { } } finally { } Use(x); } return 0;",
        "int x; switch (1) { case 1: try { if (Cond()) break; x = 1; } finally { } break; default: x = 2; break; } Use(x); return 0;",
        "int x; while (true) { try { switch (1) { case 1: continue; default: break; } } finally { } break; } Use(x); return 0;",
        // `goto`, to a label outside and to one in between.
        "int x; try { if (c) goto L; x = 1; } finally { } Use(x); return 0; L: Use(x); return 1;",
        "int x; try { if (c) goto L; } finally { } return 0; L: Use(x); return 1;",
        "int x; try { try { if (c) goto L; } finally { } L: Use(x); } finally { x = 1; } return 0;",
        "int x; int y; try { if (c) goto L; y = 1; } finally { x = 1; } L: Use(x); Use(y); return 0;",
        "int x; int n = 0; try { L: n++; if (n < 3) goto L; } finally { } Use(x); return 0;",
        "int x; if (c) { try { goto E; } finally { } } else x = 2; E: return x;",
        // A `finally` that reads before it assigns, and one that assigns in
        // a `try` with a `catch`, which may not have got to it.
        "int x; try { if (c) return 1; } finally { Use(x); x = 1; } return x;",
        "int x; try { if (c) return 1; } finally { try { x = 1; } catch { } } return x;",
        // A `using` and a `lock` assign nothing on the way out.
        "int x; using (var d = (IDisposable)null) { if (c) return 1; } return x;",
        "int x; lock (this) { if (c) return 1; } return x;",
        // In a lambda and in a local function.
        "Func<int> f = () => { int y; try { if (c) return 1; } finally { } return y; }; return f();",
        "int Local() { int y; try { if (c) return 1; } finally { } return y; } return Local();",
        "int x; try { Action f = () => { int w; goto L; L: Use(w); }; } finally { x = 1; } return x;",
        "Action f = () => { int w; try { goto L; } finally { } L: Use(w); }; return 0;",
        // What an enclosing method's `finally` assigns is not the lambda's.
        "int x; try { Func<int> f = () => { if (c) return 1; return 2; }; } finally { } Use(x); return 0;",
    ] {
        assert_eq!(only(&method(body), &["CS0165"]), ["CS0165"], "{body}");
    }
}

#[test]
fn an_out_parameter_a_jump_out_of_a_try_leaves_unassigned_is_cs0177() {
    for body in [
        "try { if (c) return; } finally { } r = 1;",
        "try { if (c) return; r = 2; } finally { }",
        "try { if (c) return; r = 2; } finally { if (c) r = 3; }",
        "try { Use(1); } catch { if (c) return; r = 1; } finally { } r = 2;",
        "try { try { return; } finally { } } finally { }",
        "try { Func<int> f = () => 1; if (c) return; } finally { } r = 1;",
    ] {
        assert_eq!(only(&with_out(body), &["CS0177"]), ["CS0177"], "{body}");
    }
    assert_eq!(
        only(
            "using System; class C { int M(out int r, bool c) { try { return 1; } finally { } } }",
            &["CS0177"]
        ),
        ["CS0177"]
    );
}

#[test]
fn what_the_finally_assigns_reaches_every_jump_out_of_the_try() {
    for body in [
        // `return`.
        "int x; try { if (c) return 1; } finally { x = 2; } return x;",
        "int x; try { if (c) return 1; x = 3; } finally { } return x;",
        "int x; try { try { if (c) return 1; } finally { } } finally { x = 1; } return x;",
        "int x; try { try { if (c) return 1; } finally { x = 1; } } finally { } return x;",
        "int x; try { return 1; } finally { x = 2; } Use(x); return 0;",
        "int x; try { } catch { if (c) return 1; x = 1; } finally { x = 5; } return x;",
        "int x; try { } catch (Exception) when (c) { return 1; } finally { x = 5; } return x;",
        "int x; try { if (c) return 1; } finally { x = c ? 1 : 2; } return x;",
        "int x; try { if (c) return 1; } finally { if (c) { x = 1; } else { x = 2; } } return x;",
        "int x; try { if (c) return 1; } finally { try { x = 1; } finally { } } return x;",
        "int x; try { if (c) return 1; } finally { for (;;) { x = 1; break; } } return x;",
        "int x = 0; int y; try { if (c) return 1; } finally { y = x; } return y;",
        "int x; try { if (c) return 1; } finally { throw new Exception(); } return x;",
        // `break` and `continue`, through one finally and through two.
        "int x; while (true) { try { if (Cond()) break; } finally { x = 1; } } Use(x); return 0;",
        "int x; for (;;) { try { try { if (Cond()) break; } finally { x = 1; } } finally { } } Use(x); return 0;",
        "int x; for (;;) { try { try { if (Cond()) break; } finally { } } finally { x = 1; } } Use(x); return 0;",
        "int x; int i = 0; while (i++ < 3) { try { if (Cond()) continue; } finally { x = 1; } Use(x); } return 0;",
        "int x; do { try { if (Cond()) continue; } finally { x = 1; } } while (x > 0); return 0;",
        "int x; switch (1) { case 1: try { if (Cond()) break; } finally { x = 1; } break; default: x = 2; break; } Use(x); return 0;",
        "int x; while (true) { try { switch (1) { case 1: continue; default: break; } } finally { x = 1; } break; } Use(x); return 0;",
        "int x; while (true) { try { Use(1); } catch { break; } finally { x = 1; } } return x;",
        // A jump that does not leave the `try` takes nothing from it.
        "int x; while (true) { while (true) { try { if (Cond()) break; } finally { } } x = 1; break; } Use(x); return 0;",
        "int x; while (true) { try { while (true) { if (Cond()) break; } x = 1; } finally { } if (Cond()) break; } Use(x); return 0;",
        "int x; int i = 0; while (i++ < 3) { try { if (Cond()) continue; x = 1; Use(x); } finally { } } return 0;",
        // `goto`, inside and out, the label before the `try` or after.
        "int x; try { if (c) goto L; } finally { x = 1; } Use(1); return 0; L: Use(x); return 1;",
        "int x; try { try { if (c) goto L; } finally { x = 1; } } finally { } return 0; L: Use(x); return 1;",
        "int x; try { try { if (c) goto L; } finally { x = 1; } L: Use(x); } finally { } return 0;",
        "int x; int n = 0; L: try { n++; if (n < 3) goto L; } finally { x = 1; } Use(x); return 0;",
        "int x; int n = 0; try { L: n++; if (n < 3) goto L; x = 1; } finally { } Use(x); return 0;",
        "int x; int n = 0; A: try { try { n++; if (n < 4) goto A; } finally { } } finally { x = 1; } Use(x); return 0;",
        "int x; try { if (c) goto L; } catch { goto L; } finally { x = 1; } L: Use(x); return 0;",
        "int x; if (c) { try { goto E; } finally { x = 1; } } else x = 2; E: return x;",
        "int x; for (;;) { try { for (;;) { try { if (c) goto Out; } finally { x = 1; } } } finally { } } Out: Use(x); return 0;",
        "int x; try { try { goto Out; } finally { if (c) x = 1; } } finally { x = 2; } Out: Use(x); return 0;",
        // A `using` or a `lock` around a `try` that assigns.
        "int x; using (var d = (IDisposable)null) { try { if (c) return 1; } finally { x = 1; } } return x;",
        "int x; using (var d = (IDisposable)null) { if (c) return 1; x = 1; } return x;",
        // Lambdas and local functions have returns of their own.
        "int x; try { Func<int> f = () => { if (c) return 1; return 2; }; } finally { x = 1; } Use(x); return 0;",
        "Func<int> f = () => { int z; try { if (c) return 1; } finally { z = 1; } return z; }; return f();",
        "int Local() { int y; try { if (c) return 1; } finally { y = 1; } return y; } return Local();",
        "Action f = () => { int w; try { goto L; } finally { w = 1; } L: Use(w); }; return 0;",
    ] {
        let found = only(&method(body), &["CS0165", "CS0177", "CS0269"]);
        assert!(found.is_empty(), "{body}: {found:?}");
    }
    for body in [
        "try { if (c) return; } finally { r = 1; }",
        "try { if (c) return; } catch { return; } finally { r = 1; }",
        "try { try { if (c) return; } finally { } } finally { r = 3; }",
        "try { try { return; } finally { r = 1; } } finally { }",
        "try { try { return; } finally { } } finally { r = 1; }",
        "while (c) { try { if (Cond()) break; } finally { r = 1; } } r = 2;",
        "try { r = 1; if (c) return; } finally { }",
        "try { Func<int> f = () => { return 1; }; } finally { r = 1; }",
    ] {
        let found = only(&with_out(body), &["CS0165", "CS0177", "CS0269"]);
        assert!(found.is_empty(), "{body}: {found:?}");
    }
    let found = only(
        "class C { int M(out int r, bool c) { try { return 1; } finally { r = 1; } } }",
        &["CS0177"],
    );
    assert!(found.is_empty(), "{found:?}");
}
