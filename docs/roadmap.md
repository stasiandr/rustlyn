# Roadmap

## What's next

The self-build has reached a fixed point, and there is no point turning it further: the
third generation is byte-for-byte equal to the second. The measure now is other people's
code.

**CompileAndVerify.** The benchmark ([`tools/cav`](../tools/cav/README.md)) of 16,785
programs with known output, extracted the way Roslyn itself compiles them (language
version, options, all files, theory rows), passes 54%. Most failures are in default
interface implementations, C# 14 extension operators and compound assignment, C# 15
unions and extension indexers, collection expressions and interpolated string handlers.
The earlier, narrower set (3,529 programs) passed 63%, and its remainder is an honest
list of what the compiler cannot do yet: `InlineArray` with `ref` `foreach` variables
and `await` around them (50 tests), natural delegate types and lambdas with default
parameter values (98), `dynamic` (70), unsafe code (95), C# 14 `extension` blocks,
expression trees with method groups, tests with a second assembly as input. Restricted
to C# 11 on net8.0 (what csc itself passes there), Rustlyn passes 78.6%; see the cav
README for the breakdown.

**Open-source libraries.** Of the libraries in [`tools/oss`](../tools/oss/README.md),
six build into assemblies and five of those are exercised by working programs; Humanizer and FluentValidation wait either for source
generators or for their generated code as input.

**Decompiler.** It reads everything Rustlyn and Roslyn write and folds lambdas, local
functions, iterators and `async` back; on `System.Linq.Enumerable` it matches ILSpy
verbatim in 278 of 476 methods. Next: `switch` from chains of comparisons with numbers
and enums (strings are done), `switch` expressions and list patterns, ranges
(`s[1..^1]` instead of `Substring`), the remaining `goto` shapes in hand-written state
machines and `?.` chains with early exit, `System.SR`, and tuple names in explicit
interface implementations.

**Smaller items.** Events in interfaces, incremental reparsing (the green nodes are
ready for it), XML in documentation comments.

**Speed.** Batch builds already beat a warm csc, and there is headroom in two places.
IL and metadata generation runs on one core (2.1 s of 6.1): tokens are assigned in
generation order, and parallelizing with the same bytes requires generating bodies with
symbolic references first and assigning tokens in a second, ordered pass. Reference
assembly symbols are loaded whole (0.16 s every run, two thirds of `hello`) rather than
on demand.

**Editor layer.** Recompiling after a save is a declaration pass over the whole project
(3 s on Roslyn), although only one tree changed: per-file declarations followed by a
merge would make it proportional to the edit. Tuple element names in positional
patterns (`(checked: true, _)`) and `nameof` inside attributes are not bound.

**Analyzers.** `rustlyn-analyzer` ([analyzer.md](analyzer.md)): the value graph and
blast radius still read some text as UTF-16 internally; move them fully onto the bound
tree and byte offsets.

## Milestones

| # | Milestone | Status |
|---|---|---|
| 0 | Workspace skeleton, CI | done |
| 1 | Text, diagnostics, lexer | done |
| 2 | Green/red tree with interning | done |
| 3 | Parser for the whole language with error recovery | done |
| 4 | Preprocessor, interpolation, raw strings, LINQ | done |
| 5 | Symbols: declaration table, namespaces, types, members, `Compilation` | done |
| 6 | Binder: name lookup, overloads, conversions, `SemanticModel` | done |
| 7 | Backend: interpreter for a subset | done |
| 8 | Bound tree | done |
| 9 | IL and metadata generation: an assembly that runs | done |
| 10 | Patterns, `switch`, `try`/`catch`/`finally` | done |
| 11 | Structs, enums, interfaces | done |
| 12 | Interpreter on the bound tree | done |
| 13 | `using`, property metadata, short branch forms | done |
| 14 | Generic types and indexers: `TypeSpec`, `MemberRef` under it | done |
| 15 | Accessors as separate symbols: user indexers, `set { ... }` | done |
| 16 | Generic methods: type inference, `!!0`, `MethodSpec` | done |
| 17 | `foreach` over an enumerator, not only arrays | done |
| 18 | Delegates: `ldftn`/`ldvirtftn`, method groups, `Invoke` | done |
| 19 | Nested types: the `NestedClass` row and their own visibility | done |
| 20 | Lambdas: binding against the delegate, closures in the interpreter | done |
| 21 | A lambda is a method: `ldftn` to it, names like `<Main>b__0` | done |
| 22 | Closure classes: a captured variable outlives the method | done |
| 23 | Records and user-defined operators | done |
| 24 | `ref` and `out`: by-ref signatures, `ldind`/`stind` | done |
| 25 | Metadata reading: PE, heaps, all §II.22 tables | done |
| 26 | Disassembler: body headers, all opcodes, handlers | done |
| 27 | Symbols from real assemblies: references instead of a synthesized corlib | done |
| 28 | Compiling against real assemblies: `AssemblyRef` from metadata, struct enumerators | done |
| 29 | Running Roslyn through the binder; enum operators | done |
| 30 | Attributes from metadata, extension methods, type inference through base types | done |
| 31 | Binder 50 times faster: `global using` was evaluated for every name | done |
| 32 | Nested namespaces in scope, `object` members on everything | done |
| 33 | `nameof`, `params`, `_`, constants that fit a narrower type | done |
| 34 | Local functions, object and collection initializers | done |
| 35 | Generic constraints, `constrained.`, static members of constructions | done |
| 36 | `?.`: conditional access evaluating the receiver once | done |
| 37 | Type inference from lambdas, one `T` per partial type | done |
| 38 | Deconstruction, `await` in the binder, returns from `async` | done |
| 39 | Named arguments, user-defined conversions, `out _` | done |
| 40 | Overloads gathered across the whole hierarchy, not up to the first hit | done |
| 41 | Substitution through a base construction, explicit interface implementations | done |
| 42 | Deconstruction in `foreach`, `ref` locals | done |
| 43 | `using static`, overload pruning per §12.6.4.5 | done |
| 44 | Discards and mixed targets in deconstruction | done |
| 45 | Nested type arguments taken from the name around it | done |
| 46 | `using` resolved relative to its own namespace | done |
| 47 | A nested type is visible through the base type too | done |
| 48 | `ref` returns read as the referenced type | done |
| 49 | `nint` and `nuint` | done |
| 50 | Operators of types outside the built-in list (`Half`, `TimeSpan`) | done |
| 51 | Omitted optional parameters are filled in | done |
| 52 | Pointers: arithmetic, indexing, `*`, `&`, `fixed` | binding |
| 53 | A `static` local function does not see surrounding locals | done |
| 54 | Tuples as values: type, element names, `ValueTuple` | binding |
| 55 | A nested type carries its enclosing type's type parameters | done |
| 56 | Struct calls go by address, `constrained.` for a foreign method | done |
| 57 | Inherited members and `: base(...)` go through the construction | done |
| 58 | LINQ queries: range variables and their types | binding |
| 59 | `is var (a, b)` and a local function as a name before its declaration | done |
| 60 | Backend coverage measurement: how many method bodies compile | done |
| 61 | An enum member is a constant of its underlying type | done |
| 62 | `throw` expressions, `throw;`, `sizeof`, `checked`, `x!` | done |
| 63 | Fields and indexers of metadata types compile | done |
| 64 | Tuples compile: `ValueTuple`, `ItemN`, element names | done |
| 65 | `goto case` and `goto default` | done |
| 66 | `lock`: `Monitor.Enter`/`Exit` in `try`/`finally` | done |
| 67 | `switch` sections side by side, not nested | done |
| 68 | `nameof` in a pattern is a constant; `foreach ((var a, var b) in …)` | done |
| 69 | Constant values computed once, not again per member | done |
| 70 | Recursive patterns: properties, `Deconstruct`, chains, `T?` | done |
| 71 | `T` to `T?` and back is a real conversion | done |
| 72 | `??=`, tuple deconstruction, lambdas in property bodies | done |
| 73 | Collection expressions: arrays, `Span<T>`, `new` + `Add` | done |
| 74 | Resource classes from `.resx`: the missing piece of the corpus | done |
| 75 | A constant that fits a narrower type reaches overload resolution too | done |
| 76 | `implicit operator` of a generic type and static members of a construction | done |
| 77 | A nested type sees what is declared in its enclosing type | done |
| 78 | A constant meets an unsigned operand; `const` has no storage | done |
| 79 | `ref` locals and `ref` returns reach IL | done |
| 80 | Lambdas in field initializers and inside local functions | done |
| 81 | A `static` lambda does not see surrounding locals; `case (a, _)` is a pattern | done |
| 82 | `out T` and `in T`: variance of constructions, array covariance | done |
| 83 | CS1503 instead of CS1501 when the argument type is at fault | done |
| 84 | Tuple element names are not part of the type; explicit type arguments | done |
| 85 | `where T : class` is a reference type; a less generic overload is better | done |
| 86 | A name after `is` that is not a type is a constant; a member hides a namespace | done |
| 87 | A struct's `: this()` is a constructor nobody wrote | done |
| 88 | A value that is not a variable gets a place so its address can be taken | done |
| 89 | A qualified name reaches a nested namespace | done |
| 90 | `default`, `new(...)` and `a ?? throw` take their type from the target | done |
| 91 | `goto` and labels | done |
| 92 | `[CollectionBuilder]`: `ImmutableArray<T>` from `[a, b]` | done |
| 93 | A value is boxed before it is asked what it is | done |
| 94 | `^k` and `a..b`: `Index`, `Range`, slices and substrings | done |
| 95 | A lambda in a block accessor belongs to the accessor | done |
| 96 | A nested function's local hides the outer one; loop conditions and unbraced branches get their own scope | done |
| 97 | `base` is the base class, `ref readonly`, `nint`, `enum >= 0`, `byte*` to `void*` | done |
| 98 | A lambda picks an overload by what it returns; type inference from a method group | done |
| 99 | `field`, primary constructors, `with`, nested deconstruction | done |
| 100 | `FormattableString`, constraints on `override`, `this ref`, inference bounds | done |
| 101 | C# 14 extension blocks, `const` locals as values, `??=` on `T?` | done |
| 102 | Natural type of lambdas, extension method groups as delegates, delegates in tuple elements | done |
| 103 | Corpus: `AnalyzerDriver`, .NET 10 and SDK-style `/define:`: 99.7% of files without diagnostics | done |
| 104 | Primary constructors: `: Base(args)`, capturing parameters into fields, record positional properties | done |
| 105 | Field-like events, `+=`/`-=` through `Delegate.Combine`, lifted `==` on `T?` with a user operator | done |
| 106 | Method groups: substitution through a construction, contravariance, a generic method as a delegate | done |
| 107 | `{x,5:N2}` via `string.Format`, `a?[i]`, `list[^1] = x`, `out var _`, `var (a, b)` as a pattern | done |
| 108 | Conditional with one typeless branch, tuples element-wise, `[]` only into a collection | done |
| 109 | `Dispose` through `IDisposable` (including explicit on a struct), `yield` in a getter, `["k"] = v` in an initializer | done |
| 110 | `async`/`await`: a state machine with a builder, `await` inside `try`/`using`/`foreach`, spilling `await` out of expressions | done |
| 111 | `yield` inside `try`/`using`/`lock`/`foreach`: entering a region by state, `Dispose` runs the `finally` | done |
| 112 | Lambdas and local functions inside a state machine: the state machine is its own display class | done |
| 113 | Unsafe code: `*p`, `&x`, `p[i]`, pointer arithmetic, `fixed` with a pinned local, `stackalloc` to `T*` and `Span<T>` | done |
| 114 | `with` for structs, tuples and record classes (`<Clone>$` and a copy constructor; `record : record` truly inherits) | done |
| 115 | `[CollectionBuilder]` from source, `{ { … }, { … } }` with no type nearby, `case []:` as a list pattern, assignment into a `ref`-returning call, `..span` in a collection expression | done |
| 116 | `async` lambdas and local functions: the closure's state machine, captures read through the display class from `<>4__this` | done |
| 117 | `yield` in a local function: the iterator belongs to the function, not the enclosing method | done |
| 118 | Lambda inside a lambda: the outer lambda has its own display class pointing at the method's, created on every call | done |
| 119 | `await` in a `while` condition, the right operand of `&&`/`\|\|`, a `?:` branch and a `catch` body; an `async` lambda infers `Task<T>` during overload resolution | done |
| 120 | `[DllImport] static extern`: `ModuleRef` and `ImplMap` tables; an `extern` local function stays a static method of the type | done |
| 121 | LINQ queries with `let`, a second `from`, multi-key `orderby` and `group … by … into`: the transparent identifier is a named tuple | done |
| 122 | The built `Roslyn.dll` made to work: `constrained.` for `Dispose` and accessors through a type parameter, `base.` to the nearest override, `castclass` for explicit reference conversions, target-typed `?:` and `switch` with incompatible branches, `ref`-returning indexers as references, fields and properties through `T : class` on a boxed value | done |
| 123 | Constraint checks in overload resolution, omitted optional arguments in the call's type, operand width of compound assignment, `decimal` through `System.Decimal` operators, lifted unary operators on `T?`, `foreach` casting the element to the declared type | done |
| 124 | Roslyn built by our compiler compiles and runs a program: `Create` → `GetDiagnostics` → `Emit` → `M(41) = 42` | done |
| 125 | Anonymous types: `new { i = k, d }` is a `<>f__AnonymousType0<…>` class with a constructor and properties, one per shape; collection initializer `{ { k, v } }` is a multi-argument `Add` | done |
| 126 | Embedded resources: `.resources` from `.resx`, the `ManifestResource` table and the resource directory in the CLI header; `ResourceManager` reads them | done |
| 127 | A foreign class's private overload is not a candidate; a `this ref` extension gets its receiver by reference; a struct's `this` is copied into an iterator's state machine; `bool? + string` is not lifted; an interpolation hole with an untyped `?:` is `object`; a default parameter value and `Color Color` do not make a struct's lambda capture `this` | done |
| 128 | A conversion operator with an `in` parameter gets the operand's address, and a generic operator's operand is cast to the construction's type (`ReadOnlySpan<char>.op_Implicit(char[])`); `ldflda` through a type parameter is taken from the reference, not from its slot | done |
| 129 | Verifier over the built Roslyn: 551 → about 200 findings. No dead `br` after `return`, a final `ret` only where reachable; `while (true)` without a test; a delegate to a struct method boxes the receiver; a generic `record` names members through its construction; `t == null` for `T` via `box`; constants loaded at the declared type's width; `c ? ref a : ref b` is a location, not a copy; and more | done |
| 130 | Type inference: an upper tuple bound from `Func<…>` beats a lower one from a tuple literal; `return` inside `try` is seen when inferring a lambda's type; 4 stubs left in the corpus, all async enumerables | done |
| 131 | Two parts of a `partial` method are one method; a pattern variable in a `?:` bound twice is declared once: **the Roslyn corpus binds with no diagnostics** | done |
| 132 | `await foreach` lowered to `GetAsyncEnumerator`, `while (await MoveNextAsync())`, `Current` and `finally { await DisposeAsync() }`; the `async` state machine rewrites `finally` containing `await` (the exception is caught and held, `return`/`break`/`continue` from `try` are deferred, then `ExceptionDispatchInfo.Throw` or the deferred exit); 2 stubs left in the corpus | done |
| 133 | **The built Roslyn compiles `src/Dependencies`** (146 files, 0 diagnostics, `Emit` gives a 352 KB assembly; ILVerify finds 38 issues: `ldsflda` of readonly fields and `ref` returns, as in csc's own output). Along the way: `throw` in an unreachable method end, `~C()` returns `void`, `[GeneratedRegex]` from the generated file, enum members in their own enum's initializer, `x as S?` as `isinst` + `unbox.any`, and others | done |
| 134 | **The built Roslyn compiles `Compilers/Core/Portable` with `AnalyzerDriver` and `Dependencies`**: 1,075 files, 0 diagnostics, a 3.3 MB assembly in 37 seconds. Along the way: fixed-size buffers (`<Buffer>e__FixedBuffer` with `ClassLayout` and `FixedElementField`), methods never end in fall-through even in dead code, `(int)nullableEnum` reads the value first, static lambdas of generic methods in generic types, `ref` parameters of closures in generic display classes | done |
| 135 | **Roslyn compiles Roslyn**: the Roslyn.dll built by Rustlyn accepts all 2,243 files of its own source, `Emit` gives Roslyn2.dll (11.4 MB, with resources), and Roslyn2 again compiles and runs all 22 check programs. Along the way: `[StructLayout(LayoutKind.Explicit)]` and `[FieldOffset]`, default parameter values and `[out]`/`[in]` in the `Param` and `Constant` tables, a display class per call for local functions whose variables a nested closure captures, `stobj` for `decimal` through a reference. The self-build driver is [`tools/selfhost/drive.cs`](../tools/selfhost/drive.cs) | done |
| 136 | **Fixed point**: second-generation Roslyn builds the corpus into the same bytes as the first (`Roslyn2 == Roslyn3`, 0 lines of IL difference), deterministically (`Roslyn2 == Roslyn2b`); 61,192 corpus bodies checked against the reference, 2 replaced by stubs. Along the way: custom attributes in metadata (`CustomAttribute` table, II.23.3 blobs, synthesized `ExtensionAttribute`/`ParamArrayAttribute`), events (`Event`/`EventMap`, events from metadata), `static abstract` interface members with `MethodImpl` and `constrained.` for generic math, `async Main`, display classes of nested lambdas with a parent chain | done |
| 137 | **CompileAndVerify as a benchmark**: 3,529 Roslyn tests of the form `CompileAndVerify(source, expectedOutput:)` extracted into programs with expected output ([`tools/cav`](../tools/cav/README.md)), each built by our `build` and run on the real runtime. From 45% on the first run to **63% (2,222 of 3,529)**. Extraction now evaluates what the test actually compiles (string concatenation, constants, options, language version, theory rows, helper methods and loops): **16,785 tests, 53.9% (9,041)**; on the earlier 3,451, 93% (3,211) | in progress |
| 138 | **Open-source libraries** ([`tools/oss`](../tools/oss/README.md)): Newtonsoft.Json, Serilog, Dapper, NodaTime, MoreLINQ and Polly bind with no diagnostics (all files) and build into assemblies with one to five stubbed bodies each; programs against them work (Newtonsoft.Json serializes, deserializes and parses `JObject`, Serilog logs to the console, NodaTime computes dates, MoreLINQ and Polly do their thing). Humanizer and FluentValidation hit source generators (their code is produced by a NuGet package at build time): a limit of the input, not the compiler | done |
| 139 | Caller info: `[CallerMemberName]`, `[CallerLineNumber]`, `[CallerFilePath]` and `[CallerArgumentExpression]` for methods, constructors, indexers and attribute constructors; optional indexer arguments; named arguments of attribute constructors | done |
| 140 | Tuple equality: `t1 == t2` element-wise, each side evaluated once and in order, nullable tuples, `t == default`; tuple literals convert into tuple types element-wise (`(byte, byte) a = (1, 2)`) and into nullable tuples | done |
| 141 | A closure in a loop body inside an `async` method gets a class per iteration, kept in a state machine field across `await`; `Equals`/`GetHashCode`/`ToString` of anonymous types; `foreach` over an unsealed class's enumerator checks `IDisposable` at run time; `await foreach` through an extension; `<Clone>$` of a record with a generic base | done |
| 142 | `checked`/`unchecked`: source regions in which `+`, `-`, `*`, `++`, `--`, compound assignment and unary minus trap overflow (`add.ovf` and family), and integer and floating narrowing uses `conv.ovf.*` | done |
| 143 | **Expression trees**: a lambda converted to `Expression<TDelegate>` is described, not compiled (`Expression.Parameter`, a factory per node, `Expression.Lambda<T>`; members named via `ldtoken` and `GetMethodFromHandle`/`GetFieldFromHandle`); plus user-defined unary operators, operators of constructed types, `explicit operator` followed by a standard conversion | done |
| 144 | Inline arrays (`[InlineArray(n)]`, C# 12): the buffer read through `MemoryMarshal.CreateSpan(ref Unsafe.As<TBuffer, T>(ref buffer), n)`, `buffer[i]`, `buffer[^1]`, `buffer[1..3]`, `foreach`, conversions to `Span<T>`/`ReadOnlySpan<T>` | done |
| 145 | Top-level statements: a file without `Main` becomes `Program.<Main>$(string[] args)` (`int`, `Task` or `Task<int>` by its `return`/`await`), local functions among statements visible to the whole file, `partial class Program` from source merged; plus several smaller features | done |
| 146 | Resumable lexer: colour the screen, not the file | done |
| 147 | Editor layer: file outline from the parser, not from line shapes | done |
| 148 | Project index and go to definition by the scope at the reference site | done |
| 149 | Assembly surface immediately, method IL on demand | done |
| 150 | C ABI and a header checked by a C program | done |
| 151 | A captured variable is fresh each time the scope that declares it is entered: a closure class per block, loop iteration, `catch`, `using`, `switch` and lambda call, nested to any depth, in iterators and `async` methods and closures too | done |
