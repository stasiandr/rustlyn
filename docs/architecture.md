# Architecture

Rustlyn is an analyzer built on a compiler: what it says about a project is read off the
same symbols and bound trees the code is compiled from. It follows Roslyn's layering:
text, syntax, symbols and binding, then backends that consume the bound tree. The
editor-facing layer reuses the same pieces, arranged so that each can answer before the
next one starts (see [editor.md](editor.md)), and the whole-project analyses sit on top
of it (see [analyzer.md](analyzer.md)).

```
source text ─► tokens ─► green/red tree ─► declarations (symbols) ─► bound tree ─┬─► IL + metadata (.dll)
                                                                                └─► interpreter
.dll ─► metadata tables ─► symbols (references) / IL disassembly / decompiled C#
```

## Crates

| Crate | Role |
|---|---|
| `rustlyn-text` | `SourceText`, `TextSpan`, mapping offsets to lines and columns |
| `rustlyn-diagnostics` | `Diagnostic`, `CSxxxx` error codes, `DiagnosticBag` |
| `rustlyn-syntax` | `SyntaxKind`, lexer, green/red tree, parser |
| `rustlyn-semantics` | symbols, declaration table, `Compilation`, binder, `SemanticModel`, loading symbols from referenced assemblies |
| `rustlyn-interpret` | an interpreter that runs what the compiler understood |
| `rustlyn-emit` | IL, ECMA-335 metadata and PE: an assembly the CLR runs |
| `rustlyn-metadata` | reading metadata and IL back: the same ECMA-335 from the other end |
| `rustlyn-decompile` | decompiler: from metadata and IL back to readable C# |
| `rustlyn-ide` | the same layers arranged for an editor: open, colour, outline, index, compile, decompile, with a cache at each layer |
| `rustlyn-ffi` | a C ABI over `rustlyn-ide`, for editors not written in Rust |
| `rustlyn-analyzer` | whole-project analyses over `rustlyn-ide`: blast radius, value graph, failability, Unity assets, NuGet |

## Key decisions inherited from Roslyn

* **Full fidelity.** The tree must reproduce the source verbatim; otherwise an IDE
  cannot hand back edited text changing only what the user touched. Everything else
  rests on this invariant, and tests check it at every level.
* **Green/red tree.** A green node knows its kind, children and width, but not where it
  is or who its parent is, so the same node can sit in two versions of a file and a
  reparse can keep untouched subtrees. Positions and parent links live in the red tree,
  built on demand during traversal and just as cheaply thrown away.
* **The parser never fails.** Missing tokens become zero-width, extra ones are folded
  into `SkippedTokensTrivia`, and text is never lost.
* **Backtracking instead of guessing.** C# is not LL(k): telling `(a)-b` from
  `(int)-b`, `a < b` from `a<b>()`, or `a.b c;` from `a.b(c);` takes a trial parse. The
  parser sets a reset point, tries, and rewinds.
* **Contextual keywords stay identifiers** and are only tagged with a `contextual_kind`
  field: deciding what `record` means at a given spot is the parser's job, not the
  lexer's.

## Decisions of its own

* **One bound tree, two backends.** The code generator and the interpreter walk the
  same bound tree. They agree because they were told the same thing, and a test runs
  programs through both and compares outputs. The backends never look at syntax, so a
  binder decision cannot be made twice differently.
* **Deterministic output regardless of threads.** Parsing, reference loading and
  binding run in parallel, but the emitted assembly is byte-for-byte the same for any
  thread count (see [performance.md](performance.md)).
* **Shared green nodes.** Tokens without a value of their own and small nodes over them
  are interned, as in Roslyn's `SyntaxNodeCache`.

Where Rustlyn knowingly behaves differently from Roslyn, it is listed in
[differences-from-roslyn.md](differences-from-roslyn.md).
