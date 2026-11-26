# Known differences from Roslyn

Places where Rustlyn knowingly behaves differently from Roslyn or from the C#
specification. Smaller, module-level differences are documented in the module that
implements the behaviour.

## Text and syntax

* Offsets are counted in UTF-8 bytes, not UTF-16 code units, because that is what
  `&str` means. Conversion happens at the API boundary where it is needed (the editor
  layer has `utf16.rs`; the `diagnose` example reports UTF-16 columns, as Roslyn does).
* Unicode identifier categories come from `std` (`is_alphabetic`, `is_alphanumeric`)
  rather than the exact `Lu/Ll/Lt/Lm/Lo/Nl/Nd/Pc/Mn/Mc/Cf`. They agree on ASCII and
  ordinary letters; rare modifier characters may differ.
* Diagnostics hang off the tree rather than green nodes. Roslyn cannot do this (its
  green nodes have no positions). This will have to change once reparsing becomes
  incremental.
* A directive is stored as a single trivia for the whole line: its internal structure
  (the condition expression) is not in the tree, although it is evaluated.
* A lone surrogate in a literal (`"\uD800"`, `'\xDFFF'`) parses and keeps its text, but
  the token value holds `U+FFFD`: a Rust `char` cannot hold it. A character constant
  takes its number from the text and is correct; in a string the surrogate stays
  `U+FFFD`. This is the one place where C# genuinely requires UTF-16.
* XML inside documentation comments is not parsed into the tree.
* Source nested too deep is CS8078 at fixed limits, not where the stack runs out:
  1,024 levels of the parser's own recursion (parentheses, blocks, type arguments,
  patterns, nested types, a `?:` inside the branch taken) and a tree 12,288 nodes deep
  however it got there. A long flat shape takes no recursion to read, so only the depth
  of its tree counts: an `else if` ladder or a chain of calls or member accesses takes two
  levels a link (about 6,100 of them), a `?:` ladder or a chain of `+`, `&&` or `[i]`
  one (about 12,200). Roslyn compiles 5,000 of each and asks the runtime how much stack
  is left, so its limit moves with the thread and the build; a fixed one gives the same
  file the same answer everywhere. Threads that bind and emit get a 1 GB stack in a
  debug build (an unoptimized binder spends up to 40 KB on a level), and 256 MB in an
  optimized one. The rest of the file is kept in the tree as skipped tokens.

## Binding and emitting

* `in` parameters are passed by reference, with `modreq(InAttribute)` wherever Roslyn
  writes it (virtual, abstract and interface members, a delegate's `Invoke`; an override
  copies the modifiers of what it overrides); calling a non-`readonly` member on an `in`
  parameter goes through a copy. But there is no check that an `in` parameter is not
  written to: that is a compiler promise, and breaking it is not yet diagnosed.
* `dynamic` is bound at run time through `CallSite` and
  `Microsoft.CSharp.RuntimeBinder`, as in Roslyn, but not everywhere: there is no
  dynamic `await` and no deconstruction of a dynamic value.
* Same-named types from different assemblies are kept apart: a `TypeRef` is looked up
  in the assembly it names, and `modreq(InAttribute)` in a library member's signature
  points at the `InAttribute` recorded there. Only when the compiler writes the reference
  itself is the name looked up (it takes its own `InAttribute` from source if declared
  there, otherwise the framework's). An assembly referenced under an `extern alias`
  (`build --reference A=lib.dll`) is not visible from the global namespace at all: its
  namespaces hang off their own root, and `A::N.T` is looked up from there.
* `__arglist(...)` as an argument parses but does not compile; the emitter reports a
  clear `EmitError` naming the construct rather than writing something wrong. .NET on
  Linux and macOS does not support varargs calls at all: a program built by Roslyn fails
  with `InvalidProgramException: Vararg calling convention not supported`. `__makeref`,
  `__refvalue` and `__reftype` work.
* The closure class is made one per member, not one per scope. For a `for` variable
  this is exactly what C# promises; for a `foreach` variable, which C# 5+ creates fresh
  on every iteration, it is not (loops inside `async` methods are an exception and get a
  class per iteration). The interpreter shares one frame and so agrees with the emitter
  rather than with C#.
* Constant folding understands literals, arithmetic on them and references to other
  constants, which is exactly what a C# constant is. Anything else gives `None`, not a
  wrong value.
* An error that says code is wrong is reported only where that is certain; where the
  binder cannot tell, it lets the code through rather than refuse code Roslyn accepts.
  CS0030 (a cast nothing can make) is judged for classes, structs, interfaces,
  delegates, arrays and tuples — not for type parameters, nor where it turns on variance
  or on an array against a collection interface. CS0121 (an ambiguous call) is judged
  for methods, constructors, indexers and extension methods whose arguments are by value
  and in position; an ambiguity that turns on a lambda, a named argument, a default left
  unfilled, a type parameter used more than once, an unsigned type or three candidates
  that tie still resolves to the first candidate. CS0122 for a nested type is reported
  where it is named through its owner (`Outer.Hidden`); by its bare name in a type
  derived from the owner it is CS0246, and inside `nameof` it is let through. CS0031 (a constant that does not fit) is
  reported for a declaration or an assignment, not for an element of an array
  initializer.
* Definite assignment follows `goto`, through a `finally` too; a body the binder did not
  fully understand gets no CS0165 at all.

## Interpreter

The interpreter exists to cross-check the code generator on a subset of the language;
it is not a .NET runtime.

* An enum value gets its name when it is boxed, exactly where IL learns its type too.
  An unboxed one is just a number, as in C#.
* An exception prints its message, not `Type: message` as .NET does: there are no type
  names at that level. The object itself is real: `catch (ArgumentException)`
  distinguishes it from `catch (InvalidOperationException)`.
* Integer widths are not distinguished (everything is computed as `i64`; narrowing
  applies only where the binder inserted a conversion), and recursion depth is capped so
  that runaway recursion is reported rather than crashing the process.
* An enumerator is drained completely before the loop starts rather than stepped: the
  loop body cannot influence what `MoveNext` returns later. Within the supported subset
  there is no visible difference, but IL behaves differently.
* There is one static member per definition, not per construction:
  `Holder<int>.Count` and `Holder<string>.Count` are the same field to it, while to the
  CLR (and to the emitter) they are different. The interpreter does not distinguish
  constructions at all: its values carry no signatures.
* `async`/`await` is rewritten into a state machine by the emitter (a class with a
  builder, as `csc` does in a debug build); the interpreter does not do this and says so.
* `Dictionary<K, V>` is a list of pairs rather than a hash table: a key is a `Value`,
  and a `Value` is not hashable (objects compare by identity, strings by text). At the
  sizes the interpreter exists for, a linear search is more honest than a hidden one.
