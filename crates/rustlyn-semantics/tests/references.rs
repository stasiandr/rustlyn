//! Binding against a real assembly rather than the synthesised core library.
//!
//! These read `System.Private.CoreLib.dll` out of an installed .NET shared
//! framework. Without one they say so and pass, because the point they make is
//! about this machine having a runtime rather than about the loader.
//!
//! Set `RUSTLYN_DOTNET` to a `dotnet` executable, or `RUSTLYN_FRAMEWORK` to a
//! shared-framework directory, to point them at one.

use std::path::PathBuf;

use rustlyn_semantics::{Binder, Compilation, SpecialConstant, SymbolId, SymbolKind, Type};

/// The shared framework directory to read assemblies out of, if there is one.
fn framework() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("RUSTLYN_FRAMEWORK") {
        let path = PathBuf::from(path);
        return path.is_dir().then_some(path);
    }
    let root = match std::env::var("RUSTLYN_DOTNET") {
        Ok(path) => PathBuf::from(path).parent()?.to_path_buf(),
        Err(_) => {
            // `DOTNET_ROOT`, then the path, then the place a manual install
            // puts it.
            let mut roots: Vec<PathBuf> = Vec::new();
            if let Ok(root) = std::env::var("DOTNET_ROOT") {
                roots.push(PathBuf::from(root));
            }
            if let Ok(paths) = std::env::var("PATH") {
                roots.extend(std::env::split_paths(&paths));
            }
            if let Ok(home) = std::env::var("HOME") {
                roots.push(PathBuf::from(home).join("dotnet"));
            }
            // A `dotnet` on the path may be a link to the install
            // (Homebrew's `/opt/homebrew/bin/dotnet`), and the framework is
            // beside the install.
            let host = roots
                .into_iter()
                .map(|directory| directory.join("dotnet"))
                .find(|candidate| candidate.is_file())?;
            std::fs::canonicalize(&host)
                .unwrap_or(host)
                .parent()?
                .to_path_buf()
        }
    };
    // One directory per installed version; the newest is as good as any.
    let mut versions: Vec<_> = std::fs::read_dir(root.join("shared/Microsoft.NETCore.App"))
        .ok()?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.is_dir())
        .collect();
    // By version, not by text: `10.0.12` is newer than `8.0.31`.
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

/// The assemblies these tests reference: the core library, and the two that
/// hold what a first program uses.
const REFERENCES: [&str; 5] = [
    "System.Private.CoreLib.dll",
    "System.Console.dll",
    "System.Collections.dll",
    "System.Collections.Immutable.dll",
    "System.Linq.dll",
];

fn references() -> Option<Vec<Vec<u8>>> {
    let directory = framework()?;
    REFERENCES
        .iter()
        .map(|name| std::fs::read(directory.join(name)).ok())
        .collect()
}

/// A compilation of `source` against the real assemblies.
macro_rules! against_corlib {
    ($source:expr) => {{
        let Some(bytes) = references() else {
            eprintln!("no .NET shared framework found; skipping");
            return;
        };
        let images: Vec<&[u8]> = bytes.iter().map(Vec::as_slice).collect();
        let tree = rustlyn_syntax::parse(rustlyn_text::SourceText::new("Program.cs", $source));
        (
            bytes.len(),
            Compilation::create_with_references(vec![tree], &images),
        )
    }};
}

#[test]
fn the_core_library_declares_its_types() {
    let (_, compilation) = against_corlib!("");
    let symbols = compilation.symbols();

    for name in [
        "System.Object",
        "System.String",
        "System.Int32",
        "System.Console",
        "System.Collections.Generic.List`1",
        "System.Collections.Generic.IEnumerable`1",
        "System.IDisposable",
        "System.Exception",
    ] {
        let id = compilation
            .type_by_metadata_name(name)
            .unwrap_or_else(|| panic!("{name} should have been loaded"));
        assert_eq!(symbols.qualified_name(id), name);
        assert!(
            compilation.is_from_metadata(id),
            "{name} came from metadata"
        );
    }
}

#[test]
fn a_type_knows_what_flavour_it_is() {
    use rustlyn_semantics::TypeKind;
    let (_, compilation) = against_corlib!("");
    let kind = |name: &str| {
        compilation
            .type_by_metadata_name(name)
            .map(|id| compilation.symbols().get(id).type_kind())
    };
    assert_eq!(kind("System.Object"), Some(Some(TypeKind::Class)));
    assert_eq!(kind("System.Int32"), Some(Some(TypeKind::Struct)));
    assert_eq!(kind("System.IDisposable"), Some(Some(TypeKind::Interface)));
    assert_eq!(kind("System.DayOfWeek"), Some(Some(TypeKind::Enum)));
    assert_eq!(kind("System.Action"), Some(Some(TypeKind::Delegate)));
}

#[test]
fn a_method_keeps_its_signature() {
    let (_, compilation) = against_corlib!("");
    let symbols = compilation.symbols();
    let binder = rustlyn_semantics::Binder::new(&compilation);
    let mut sink = rustlyn_semantics::Diagnostics::new();

    let string = compilation
        .type_by_metadata_name("System.String")
        .expect("System.String");
    // `int System.String.IndexOf(string)`, which says the return type, the
    // parameter type and that it takes a `this` all at once.
    let index_of = symbols
        .lookup(string, "IndexOf")
        .iter()
        .copied()
        .find(|id| {
            let parameters = symbols.get(*id).as_method().unwrap().parameters.clone();
            parameters.len() == 1
                && binder.type_of(parameters[0], &mut sink)
                    == Type::named(compilation.type_by_metadata_name("System.String").unwrap())
        })
        .expect("string.IndexOf(string)");
    assert_eq!(
        binder.type_of(index_of, &mut sink),
        Type::named(compilation.type_by_metadata_name("System.Int32").unwrap())
    );
    assert!(
        !symbols
            .get(index_of)
            .modifiers
            .contains(rustlyn_semantics::Modifiers::STATIC)
    );
}

#[test]
fn a_generic_type_keeps_its_parameters() {
    let (_, compilation) = against_corlib!("");
    let symbols = compilation.symbols();
    let list = compilation
        .type_by_metadata_name("System.Collections.Generic.List`1")
        .expect("List`1");
    let detail = symbols.get(list).as_named_type().expect("a named type");
    assert_eq!(detail.arity, 1);
    assert_eq!(detail.type_parameters.len(), 1);
    assert_eq!(symbols.get(detail.type_parameters[0]).name, "T");

    // `T List<T>.this[int]` — an indexer, whose type is the type parameter and
    // not anything a name could have resolved to.
    let binder = rustlyn_semantics::Binder::new(&compilation);
    let mut sink = rustlyn_semantics::Diagnostics::new();
    let indexer = symbols
        .lookup(list, "this[]")
        .first()
        .copied()
        .expect("an indexer");
    assert_eq!(
        binder.type_of(indexer, &mut sink),
        Type::TypeParameter(detail.type_parameters[0])
    );
    let property = symbols.get(indexer).as_property().expect("a property");
    assert!(property.is_indexer);
    assert!(property.getter.is_some() && property.setter.is_some());
}

#[test]
fn a_type_knows_what_it_derives_from() {
    let (_, compilation) = against_corlib!("");
    let binder = rustlyn_semantics::Binder::new(&compilation);
    let object = compilation.type_by_metadata_name("System.Object").unwrap();
    let exception = compilation
        .type_by_metadata_name("System.Exception")
        .unwrap();
    let argument = compilation
        .type_by_metadata_name("System.ArgumentException")
        .unwrap();

    assert!(binder.base_types_of(object).is_empty());
    assert_eq!(
        binder.base_types_of(exception).first(),
        Some(&Type::named(object))
    );
    let bases = binder.base_types_of(argument);
    assert_eq!(
        bases.first(),
        Some(&Type::named(
            compilation
                .type_by_metadata_name("System.SystemException")
                .unwrap()
        ))
    );

    // `List<T>` implements `IList<T>`, which is a construction rather than a
    // bare name: the interface row holds a `TypeSpec`.
    let list = compilation
        .type_by_metadata_name("System.Collections.Generic.List`1")
        .unwrap();
    let ilist = compilation
        .type_by_metadata_name("System.Collections.Generic.IList`1")
        .unwrap();
    let parameter = compilation
        .symbols()
        .get(list)
        .as_named_type()
        .unwrap()
        .type_parameters[0];
    assert!(binder.base_types_of(list).contains(&Type::Named {
        symbol: ilist,
        type_arguments: vec![Type::TypeParameter(parameter)],
    }));
}

#[test]
fn the_special_types_resolve_to_metadata() {
    use rustlyn_semantics::SpecialType;
    let (_, compilation) = against_corlib!("");
    for special in [
        SpecialType::Object,
        SpecialType::String,
        SpecialType::Int32,
        SpecialType::Boolean,
        SpecialType::Void,
    ] {
        let id = compilation
            .special_type(special)
            .unwrap_or_else(|| panic!("{special:?} should resolve"));
        assert_eq!(
            compilation.symbols().qualified_name(id),
            special.metadata_name()
        );
        assert_eq!(compilation.symbols().get(id).kind, SymbolKind::NamedType);
    }
}

#[test]
fn a_nested_type_declares_only_its_own_parameters() {
    let (_, compilation) = against_corlib!("");
    let symbols = compilation.symbols();
    // `Dictionary<TKey, TValue>.Enumerator` repeats both of its enclosing
    // type's parameters in metadata and declares neither in C#.
    let enumerator = compilation
        .type_by_metadata_name("System.Collections.Generic.Dictionary`2+Enumerator")
        .expect("Dictionary`2+Enumerator");
    let detail = symbols
        .get(enumerator)
        .as_named_type()
        .expect("a named type");
    // Its arity is what C# sees — none — and its parameter list is what a
    // signature numbers, which includes the two it inherits.
    assert_eq!(detail.arity, 0);
    assert_eq!(detail.type_parameters.len(), 2);
    let inherited: Vec<Type> = detail
        .type_parameters
        .iter()
        .copied()
        .map(Type::TypeParameter)
        .collect();

    let dictionary = compilation
        .type_by_metadata_name("System.Collections.Generic.Dictionary`2")
        .expect("Dictionary`2");
    assert_eq!(symbols.get(enumerator).container, Some(dictionary));

    // Its `Current` is still `KeyValuePair<TKey, TValue>`, which it can only
    // spell with parameters it does not declare.
    let binder = rustlyn_semantics::Binder::new(&compilation);
    let mut sink = rustlyn_semantics::Diagnostics::new();
    let current = symbols
        .lookup(enumerator, "Current")
        .first()
        .copied()
        .expect("Current");
    let pair = compilation
        .type_by_metadata_name("System.Collections.Generic.KeyValuePair`2")
        .expect("KeyValuePair`2");
    let arguments = inherited;
    assert_eq!(
        binder.type_of(current, &mut sink),
        Type::Named {
            symbol: pair,
            type_arguments: arguments,
        }
    );
}

#[test]
fn a_program_binds_against_the_real_assemblies() {
    let (_, compilation) = against_corlib!(
        r#"
        using System;
        using System.Collections.Generic;

        class Program
        {
            static void Main()
            {
                List<string> names = new List<string>();
                names.Add("world");
                foreach (string name in names)
                {
                    Console.WriteLine("hello, " + name);
                }
            }
        }
        "#
    );
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
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn a_nested_type_takes_its_arguments_from_the_name_around_it() {
    // `Dictionary<string, int>.Enumerator` writes nothing after `Enumerator`
    // and still has two type arguments, because the type repeats its
    // enclosing type's parameters as its own. Getting that wrong leaves the
    // members substituted with the wrong types, which shows up as `TKey`
    // failing to convert to `TKey`.
    let (_, compilation) = against_corlib!(
        r#"
        using System.Collections.Generic;

        class Program
        {
            static string First(Dictionary<string, int> map)
            {
                Dictionary<string, int>.Enumerator walker = map.GetEnumerator();
                walker.MoveNext();
                KeyValuePair<string, int> pair = walker.Current;
                string key = pair.Key;
                int value = pair.Value;
                return key + value;
            }
        }
        "#
    );
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn a_ref_return_reads_as_the_type_it_refers_to() {
    // `ref T M()` gives back a variable, and C# calls that variable a `T`.
    // Only a `ref` assignment cares about the difference, and that is spelled
    // out in the syntax rather than carried in the type — so reading one,
    // writing through it and returning it all have to work.
    let (_, compilation) = against_corlib!(
        r#"
        class Slot<T>
        {
            private T[] _items = new T[4];

            public ref T this[int index] { get { return ref _items[index]; } }

            public ref T First() { return ref this[0]; }

            public T Read() { return this[1]; }

            public void Write(T value) { this[2] = value; }

            // `nint` and `nuint` are spellings of two framework types.
            public static nint Size(nuint count) { return (nint)count; }
        }
        "#
    );
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn a_query_brings_its_range_variables_into_scope() {
    // The translation into `Where`/`Select` calls is not done — a query is
    // emitted by neither backend — but the code around one has to make sense,
    // and that means the range variables exist and have the types their
    // collections give them.
    let (_, compilation) = against_corlib!(
        r#"
        using System.Collections.Generic;

        class Program
        {
            static void M(List<string> names, List<int> numbers)
            {
                var picked = from name in names
                             where name.Length > 2
                             let upper = name.ToUpper()
                             orderby name.Length descending, name
                             select upper + name.Length;

                var grouped = from n in numbers
                              group n by n % 2 into bucket
                              select bucket.Key;

                var joined = from name in names
                             join int n in numbers on name.Length equals n
                             select name + n;

                foreach (string one in picked) { one.Trim(); }
                foreach (int key in grouped) { key.ToString(); }
                foreach (string both in joined) { both.Trim(); }
            }
        }
        "#
    );
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn a_var_pattern_takes_a_value_apart() {
    // `x is var (a, b)` declares two variables and means the same thing a
    // deconstruction does. On a `T?` it takes the `T` apart: reaching the
    // designation has already established there is one.
    let (_, compilation) = against_corlib!(
        r#"
        class Host
        {
            public (string, int)? TryGet(string name) { return null; }
        }

        class Program
        {
            static int Read(Host host, string name)
            {
                if (host.TryGet(name) is not var (text, count)) { return 0; }
                return text.Length + count;
            }
        }
        "#
    );
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn a_static_field_and_an_indexer_of_a_framework_type() {
    // `int.MaxValue` is an ordinary static field of an ordinary framework
    // type, and `items[0]` reaches the indexer the type itself declares —
    // not one of the several explicit interface implementations beside it,
    // which C# cannot name that way at all.
    let (_, compilation) = against_corlib!(
        r#"
        using System.Collections.Generic;

        class Program
        {
            static string First(List<string> items) { return items[0]; }
            static int Max() { return int.MaxValue; }
            static string None() { return string.Empty; }
        }
        "#
    );
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");

    let symbols = compilation.symbols();
    let list = compilation
        .type_by_metadata_name("System.Collections.Generic.List`1")
        .expect("List`1");
    // One `this[]`, not one per interface the type implements.
    assert_eq!(symbols.lookup(list, "this[]").len(), 1);
    let indexer = symbols.lookup(list, "this[]")[0];
    let property = symbols.get(indexer).as_property().expect("a property");
    assert!(property.has_get && property.has_set);
}

#[test]
fn a_nested_function_is_a_method_of_its_own() {
    // The parameter of a local function hides the local of the same name
    // outside it; an `async` one returns the `T` of its `ValueTask<T>`, and
    // so does an `async` lambda given a `Func<_, Task<_>>`; and a getter with
    // a block declares local functions like any other body, `@this` and all.
    let (_, compilation) = against_corlib!(
        r#"
        using System;
        using System.Threading.Tasks;

        class Program
        {
            static int Count
            {
                get
                {
                    return local(3);
                    static int local(int @this) => @this + 1;
                }
            }

            static void M()
            {
                object binary = null;
                void visit(string binary) { Console.WriteLine(binary.Length); }
                async ValueTask<int> compute(int x) { await Task.Yield(); return x; }
                Func<int, Task<int>> f = async x => { await Task.Yield(); return x; };
                visit("a");
            }
        }
        "#
    );
    // The outer `binary` is never read, which Roslyn warns about too
    // (CS0219); nothing is an error.
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .filter(|entry| entry.diagnostic.is_error())
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn base_names_the_class_and_not_an_interface_beside_it() {
    // `Derived : Base, IHasType` chains its constructor to `Base` and reads
    // `base.Type` off `Base`, whatever else is listed after the colon.
    let (_, compilation) = against_corlib!(
        r#"
        interface IHasType { object Type { get; } }
        class Base
        {
            public Base(int a, string b, object c, bool d) { }
            public virtual object Type => null;
        }
        class Derived : Base, IHasType
        {
            public Derived(int a, string b, object c) : base(a, b, c, true) { }
            public new object Type => base.Type;
        }
        "#
    );
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn the_conversions_and_operators_roslyn_leans_on() {
    // `ref readonly` takes an `in` or a `ref` argument; `null` reaches a type
    // parameter constrained to a class; `nint` has an integer's operators
    // even though the runtime spells it `IntPtr`; a constant `0` is a value of
    // every enum, in a comparison too; and every pointer reaches `void*`.
    let (_, compilation) = against_corlib!(
        r#"
        using System.Runtime.CompilerServices;
        using System.Runtime.InteropServices;

        struct Info { public int N; }
        class Node { }

        class Program
        {
            static Info Replace(ref readonly Info info) => info;
            static T Find<T>(bool ok) where T : Node => ok ? null : null;

            static unsafe void M(Info info, UnmanagedType kind, nint p, nint q, uint u, nuint v, byte* data)
            {
                var a = Replace(in info);
                var b = Replace(ref info);
                bool ok = kind >= 0;
                bool less = p < q;
                bool more = u > v;
                nint sum = p + q;
                bool unboxed = (nint)(object)p < (nint)(object)q;
                uint r = Unsafe.ReadUnaligned<uint>(data);
            }
        }
        "#
    );
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn a_lambda_says_which_overload_by_what_it_returns() {
    // `Sum(x => x.TotalSeconds)` is the `double` overload however early the
    // `int` one is declared; `Max(info => info.Number)` on an enum reaches
    // the generic `Max<TSource, TResult>`; `Task.Run(() => Work())` keeps the
    // result rather than dropping it into an `Action`; a method group says
    // what `Select` gives back; and two arguments for one `T` fix it to the
    // type both reach.
    let (_, compilation) = against_corlib!(
        r#"
        using System;
        using System.Collections.Generic;
        using System.Collections.Immutable;
        using System.Linq;
        using System.Threading.Tasks;

        enum State { A = 1, B }
        struct Info { public State Number; public TimeSpan Span; }
        class Base { }
        class Derived : Base { }

        class Program
        {
            static int Work() => 1;
            static string Text(int n) => n.ToString();

            static void M(ImmutableArray<Info> infos, Info[] array, Derived d, Base b)
            {
                double total = infos.Sum(info => info.Span.TotalSeconds);
                long ticks = array.Sum(info => info.Span.Ticks);
                State max = infos.Max(info => info.Number);
                Task<int> task = Task.Run(() => Work());
                IEnumerable<string> texts = array.Select(info => (int)info.Number).Select(Text);
                ImmutableArray<Base> both = ImmutableArray.Create(d, b);
            }
        }
        "#
    );
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

/// Lambdas inside lambdas. A call's lambda is bound against each candidate's
/// delegate, and more than once against one, and a lambda inside it again for
/// every binding of the one around it: `Task.Run(async () => { …
/// Task.Run(async () => …` five deep took a second and each level took six
/// times the last (found by fuzzing, `examples/fuzz.rs` in rustlyn-ide).
#[test]
fn a_lambda_inside_lambdas_is_bound_once_for_each_delegate() {
    let mut runs = String::from("int answer = 42; Console.WriteLine(answer);");
    for _ in 0..7 {
        runs = format!("Task.Run(async () => {{ await Task.Delay(1); {runs} }});");
    }
    let mut sums = String::from("answer");
    for depth in 0..8 {
        sums = format!("items.Select(v{depth} => {sums} + v{depth}).Sum()");
    }
    let source = format!(
        "using System; using System.Collections.Generic; using System.Linq; \
         using System.Threading.Tasks;
         class Program {{
             static void Runs() {{ {runs} }}
             static int Sums(List<int> items) {{ int answer = 1; return {sums}; }}
         }}"
    );
    let started = std::time::Instant::now();
    let (_, compilation) = against_corlib!(source.as_str());
    // The inner `Task.Run(...)` calls are left unawaited in `async` lambdas,
    // which Roslyn warns about (CS4014); only an error is a failure here.
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .filter(|entry| entry.diagnostic.is_error())
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    assert!(
        started.elapsed().as_secs() < 10,
        "took {:?}",
        started.elapsed()
    );
}

#[test]
fn patterns_operators_and_initializers_roslyn_writes() {
    // A relational pattern on an `int?` leaves an `int` for the `var` after
    // the `and`; `!` lifts onto a `bool?`; pointers compare; a constant `0`
    // reaches an enum through the `?`; an array has a `Length` to match on;
    // an array of a derived type is an array of the base; the indexer is
    // picked by its argument; `Vector128<T>` brings its own operators; a
    // tuple alias takes an object initializer by element name; `??` widens
    // to the right when the left reaches it; and an alias for a
    // construction is that construction, arguments and all.
    let (_, compilation) = against_corlib!(
        r#"
        using System;
        using System.Collections.Immutable;
        using System.Runtime.Intrinsics;
        using Info = (string Name, int Count);
        using Numbers = System.Collections.Immutable.ImmutableArray<int>;

        enum Kind { None, Some }
        class Base { }
        class Derived : Base { }
        class Index<T> where T : class
        {
            public int this[T item] => 0;
            public T this[int row] => null;
        }

        class Program
        {
            static unsafe void M(
                int? maybe, bool? flag, char* p, char* q, Kind? kind, int[] numbers,
                Derived[] derived, Index<Base> index, Vector128<ulong> a, Vector128<ulong> b,
                object alias, string text)
            {
                if (maybe is > 0 and var n) { int m = n; }
                bool? not = !flag;
                bool less = p < q;
                bool zero = kind >= 0;
                bool empty = numbers is { Length: 0 };
                Base[] bases = derived;
                Base found = index[0];
                int row = index[found];
                Vector128<ulong> sum = (a + b) ^ a;
                Info info = new Info { Name = text, Count = 1 };
                object either = text ?? alias;
                Numbers items = Numbers.Empty.Add(3);
            }
        }
        "#
    );
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn what_c_sharp_twelve_and_fourteen_added() {
    // A primary constructor's parameters are in scope throughout the type;
    // `field` in an accessor is the property's backing field; `with` copies
    // a record; `var ((a, b), c)` and `foreach (var (k, (lo, hi)) in map)`
    // take a value apart at two levels; an override's type parameter has
    // the overridden method's constraint; an extension on `this ref` takes
    // its receiver without a `ref`; an extension on `int[]` is not
    // `Array.BinarySearch`; and an interpolated string handed to a
    // `FormattableString` keeps its holes apart from its text.
    let (_, compilation) = against_corlib!(
        r#"
        using System;
        using System.Collections.Generic;

        static class ArrayExtensions
        {
            internal static int BinarySearch(this int[] array, int value) => 0;
            internal static void AddIfNotNull<T>(this ref Holder<T> holder, T? item) where T : class { }
        }
        ref struct Holder<T> { public int Count; }
        class Node { }
        class Leaf : Node { public string Name; }
        abstract class Rewriter
        {
            public abstract List<TNode> VisitList<TNode>(List<TNode> list) where TNode : Node;
            protected void AddTrivia(Node node) { }
        }
        class Remover : Rewriter
        {
            public override List<TNode> VisitList<TNode>(List<TNode> list)
            {
                foreach (var node in list) { AddTrivia(node); }
                return list;
            }
        }
        class Scope(Leaf analyzer, int depth)
        {
            private Leaf Analyzer { get; } = analyzer;
            public int Depth => depth + 1;
            public string Name
            {
                get => field ?? "";
                set => field = value.Trim();
            }
        }
        readonly record struct Info(int Receiver, bool Cloning);

        class Program
        {
            static void M(
                int[] arities, Holder<Leaf> holder, Info info,
                (string Name, (int First, int Second) Range) pair,
                Dictionary<string, (int, int)> map, FormattableString f, IFormattable g)
            {
                int index = arities.BinarySearch(3);
                holder.AddIfNotNull(new Leaf());
                var copy = info with { Receiver = 1, Cloning = false };
                var ((name, value), isProperty, typeCode) = ((pair.Name, 2), true, 3);
                var (label, (first, second)) = pair;
                foreach (var (key, (lo, hi)) in map) { Console.WriteLine(key.Length + lo + hi); }
                Console.WriteLine(name.Length + value + typeCode + label.Length + first + second);
                f = $"{index:G9} items";
                string text = FormattableString.Invariant($"{index,5:G9}");
                g = $"{index}";
            }
        }
        "#
    );
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        // A warning (`string?` outside a `#nullable` context) is not a
        // failure to compile.
        .filter(|entry| entry.diagnostic.is_error())
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn extension_blocks_constants_and_the_shapes_between() {
    // An `extension(T x)` block (C# 14) declares members read off the
    // receiver, properties included, in patterns too; a `const` local is its
    // value wherever it is named, so a `static` lambda may name one and
    // `RT_ICON + 11` folds; `sizeof(int)` folds; `a ??= b` on a `T?` is a
    // `T`; a discard in a deconstruction is not a local called `_`;
    // `[.., x] all` names the list it matched; a lambda with a lambda inside
    // still says what it returns; a typed local is in scope in its own
    // initializer; `null` reaches a `ReadOnlySpan<byte>`; a `T?` boxes to an
    // interface its `T` implements; and an alias wins over a class of the
    // same name that a `using` brings in.
    let (_, compilation) = against_corlib!(
        r#"
        using System;
        using System.Collections.Generic;
        using System.Collections.Immutable;
        using System.Linq;
        using Options = System.Collections.Immutable.ImmutableDictionary<string, string>;
        using WORD = System.UInt16;

        class TypeSymbol { public bool IsUnion; public ImmutableArray<Param> Parameters; public List<Param> More; }
        class Param { public int RefKind; public TypeSymbol Type; }
        readonly struct Escape
        {
            public void Deconstruct(out TypeSymbol? parameter, out Param argument, out int refKind)
            {
                parameter = null; argument = null; refKind = 0;
            }
        }
        static class TypeSymbolExtensions
        {
            extension(TypeSymbol patternInputType)
            {
                public bool IsSubjectForUnionMatching => patternInputType.IsUnion;
                public bool IsUnionMatchingInputType(out TypeSymbol unionType)
                {
                    unionType = patternInputType;
                    return patternInputType.IsUnion;
                }
            }
        }
        enum Kind { A, B }

        class Program
        {
            static Kind? lazy;
            static Kind Get() => lazy ??= Kind.B;
            static IReadOnlyDictionary<string, string> Map(bool ok, Options map) => ok ? null : map;
            static bool Infer(Param argument, out int x) { x = 1; return argument.RefKind == 0; }

            static void M(TypeSymbol input, IEnumerable<TypeSymbol> many, List<Escape> escapes, int bits, Func<int, int> f)
            {
                const WORD RT_ICON = 3;
                const WORD RT_GROUP_ICON = RT_ICON + 11;
                const int IntSize = sizeof(int) * 8;
                uint index = (uint)bits / IntSize;
                Func<int, int> g = static x => x + RT_GROUP_ICON;
                if (input?.IsUnionMatchingInputType(unionType: out _) == true) { }
                bool subject = input.IsSubjectForUnionMatching && input is { IsSubjectForUnionMatching: true };
                if (input is TypeSymbol { Parameters: [.., { RefKind: 0, Type: { } last }] all } && last.IsUnion) { Console.WriteLine(all.Length); }
                var types = many.SelectMany(s => s.More.Select(p => p.Type));
                foreach (var (_, argument, refKind) in escapes) { if (Infer(argument, out _)) { Console.WriteLine(refKind); } }
                int total = total = bits + 1;
                ReadOnlySpan<byte> empty = null;
                Options.Builder builder = Options.Empty.ToBuilder();
                Console.WriteLine(index + total + g(1) + subject.GetHashCode() + types.Count() + empty.Length + builder.Count);
            }
        }
        "#
    );
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        // A warning (`string?` outside a `#nullable` context) is not a
        // failure to compile.
        .filter(|entry| entry.diagnostic.is_error())
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn delegates_where_the_corpus_keeps_them() {
    // A lambda given to `var` has a delegate type of its own when every
    // parameter is written; an extension method named on a value is a method
    // group closed over it; a delegate held in a tuple element is called
    // through the element; a candidate whose delegate returns exactly what
    // the lambda does beats one that takes the value through a conversion;
    // named arguments reach an extension call; `foreach` walks the `T`
    // inside a `T?`; and an `out var` beside a delegate lets the delegate
    // say what `T` is.
    let (_, compilation) = against_corlib!(
        r#"
        using System;
        using System.Collections.Generic;
        using System.Collections.Immutable;
        using System.Linq;
        using System.Threading;
        using System.Threading.Tasks;

        class Symbol { }
        class TypeSymbol { }
        delegate bool Extractor<T>(out T value, ref int reader);
        static class Ext
        {
            public static bool Holds(this Symbol containing, TypeSymbol type) => true;
            public static bool Check(this Symbol s, string map, int nullabilityOpt, ref int useSite, bool skip = false, HashSet<int> ignoreOpt = null) => true;
        }
        static class Runner
        {
            public static Task Run<TArgs>(Func<string, TArgs, CancellationToken, Task> consume, TArgs args, CancellationToken token) => Task.CompletedTask;
            public static Task<TResult> Run<TArgs, TResult>(Func<string, TArgs, CancellationToken, Task<TResult>> consume, TArgs args, CancellationToken token) => Task.FromResult<TResult>(default);
            public static Task<TResult> Channel<TArgs, TResult>(Func<Action<int>, TArgs, CancellationToken, Task> produce, Func<string, TArgs, CancellationToken, Task<TResult>> consume, TArgs args, CancellationToken token) => null;
        }

        class Program
        {
            static Task<int> Count(string s, CancellationToken token) => Task.FromResult(s.Length);
            static bool TryExtract<T>(int handle, out T value, Extractor<T> extractor) { value = default; return false; }
            static readonly Extractor<Symbol> s_extractor = null;

            static Task<TResult> Bridge<TArgs, TResult>(Func<Action<int>, TArgs, CancellationToken, Task> produceItems, Func<string, TArgs, CancellationToken, Task<TResult>> consumeItems, TArgs args, CancellationToken cancellationToken)
            {
                return Runner.Channel(
                    produce: static (callback, args, cancellationToken) => args.produceItems(callback, args.args, cancellationToken),
                    consume: static (items, args, cancellationToken) => args.consumeItems(items, args.args, cancellationToken),
                    args: (produceItems, consumeItems, args),
                    cancellationToken);
            }

            static async Task<int> M(Symbol symbol, ImmutableArray<TypeSymbol> types, ImmutableArray<int>? maybe, CancellationToken token)
            {
                var creation = static (Symbol context, int ordinal) => new TypeSymbol();
                TypeSymbol made = creation(symbol, 1);
                bool all = types.All(symbol.Holds);
                int useSite = 0;
                bool ok = symbol.Check("x", nullabilityOpt: 1, ref useSite, ignoreOpt: null);
                int length = await Runner.Run((s, args, ct) => Count(s, ct), args: 3, token);
                int total = 0;
                if (maybe != null) { foreach (var n in maybe) { total += n; } }
                var found = TryExtract(1, out var data, s_extractor) ? data : null;
                return length + total + (all ? 1 : 0) + (ok ? 1 : 0) + (found is null ? 0 : 1) + (made is null ? 0 : 1);
            }
        }
        "#
    );
    let diagnostics: Vec<String> = compilation
        .semantic_diagnostics()
        .iter()
        .map(|entry| compilation.render(entry))
        .collect();
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

fn error_codes(compilation: &Compilation) -> Vec<String> {
    compilation
        .semantic_diagnostics()
        .into_iter()
        .filter(|entry| entry.diagnostic.is_error())
        .map(|entry| entry.diagnostic.code().to_string())
        .collect()
}

#[test]
fn await_takes_no_user_defined_conversion_into_an_extension_getawaiter() {
    // UniTask's `GetAwaiter(this AsyncOperationHandle)` beside
    // `GetAwaiter<T>(this AsyncOperationHandle<T>)`, awaited in a generic
    // method: the handle reaches the first only through its implicit
    // operator, which a receiver may not use (§12.8.10.3), so `await` gives
    // the `T`.
    let (_, compilation) = against_corlib!(
        "using System;
using System.Runtime.CompilerServices;
using System.Threading.Tasks;
struct Handle { }
struct Handle<T> { public static implicit operator Handle(Handle<T> h) => default; }
struct Awaiter : INotifyCompletion { public bool IsCompleted => true; public void GetResult() { } public void OnCompleted(Action a) { } }
struct Awaiter<T> : INotifyCompletion { public bool IsCompleted => true; public T GetResult() => default; public void OnCompleted(Action a) { } }
static class Extensions
{
    public static Awaiter GetAwaiter(this Handle handle) => default;
    public static Awaiter<T> GetAwaiter<T>(this Handle<T> handle) => default;
}
class Loader
{
    static Handle<T> Load<T>() => default;
    static async Task<T> LoadAsset<T>() where T : class { return await Load<T>(); }
}"
    );
    assert_eq!(error_codes(&compilation), Vec::<String>::new());
}

#[test]
fn an_array_of_arrays_is_a_list_of_lists_its_elements_are() {
    // ProBuilder's `Triangulate(points, holes2d, …)` passes a `Vector2[][]`
    // for an `IList<IList<Vector2>>`: `S[]` is an `IList<T>` wherever `S` is
    // a `T` by a reference conversion (§10.2.8), and a `Vector2[]` is an
    // `IList<Vector2>`.
    let (_, compilation) = against_corlib!(
        "using System.Collections.Generic;
struct Vector2 { }
class Triangulation
{
    static bool Triangulate(IList<IList<Vector2>> holes) => holes.Count > 0;
    static bool M(Vector2[][] holes) => Triangulate(holes);
}"
    );
    assert_eq!(error_codes(&compilation), Vec::<String>::new());
}

/// The constant at `path`, as the debugger would print it.
fn constant_at(compilation: &Compilation, path: &str) -> Option<String> {
    Binder::new(compilation)
        .constant_value(symbol_at(compilation, path))
        .map(|value| format!("{value:?}"))
}

fn symbol_at(compilation: &Compilation, path: &str) -> SymbolId {
    compilation
        .symbols()
        .iter()
        .find(|symbol| compilation.symbols().qualified_name(symbol.id) == path)
        .unwrap_or_else(|| panic!("no symbol named {path}"))
        .id
}

/// The scale, sign and the three words a `decimal` constant is made of, as
/// `[DecimalConstant]` holds them.
fn decimal_at(compilation: &Compilation, path: &str) -> Option<(u8, bool, u32, u32, u32)> {
    match Binder::new(compilation).special_constant(symbol_at(compilation, path))? {
        SpecialConstant::Decimal {
            scale,
            negative,
            hi,
            mid,
            lo,
        } => Some((scale, negative, hi, mid, lo)),
        SpecialConstant::DateTime(_) => None,
    }
}

/// The codes of the errors of a program, in the order of where they are.
fn errors_in_order(compilation: &Compilation) -> Vec<String> {
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
fn a_decimal_constant_is_what_system_decimal_works_it_out_to() {
    // The words below are what `decimal.GetBits` gave in the framework for
    // each of these, which is what Roslyn writes into `[DecimalConstant]`.
    let source = "enum E : byte { A = 3, B = 200 }
    class C {
        const decimal L = (decimal)3.5;
        const decimal N = 100m / 3;
        const decimal T = 10 / 4m;
        const decimal V = (decimal)1.5f;
        const decimal W = -(decimal)0.25;
        const decimal Third = 1m / 3;
        const decimal TwoThirds = 2m / 3;
        const decimal Trailing = 1.50m;
        const decimal Product = 1.5m * 2.0m;
        const decimal NegZero = -0m;
        const decimal NegZeroProduct = 1m * -0m;
        const decimal Max = decimal.MaxValue;
        const decimal Min = decimal.MinValue;
        const decimal NearMax = decimal.MaxValue - 0.4m;
        const decimal Tiny = 0.0000000000000000000000000001m * 0.1m;
        const decimal Sum = 0.1m + 0.20m;
        const decimal Rem = 5.5m % 2m;
        const decimal RemNeg = -7m % 3m;
        const decimal FromFloat = (decimal)0.1f;
        const decimal FromDouble = (decimal)0.1;
        const decimal FromBig = (decimal)1.2345678901234567e20;
        const decimal FromSmall = (decimal)1e-5;
        const decimal FromLost = (decimal)1e-30;
        const decimal FromEnum = (decimal)E.B + 1;
        const decimal FromChar = 'a' + 0.5m;
        const decimal Nested = ((1.5m + 2) * (3 - 1m)) / 4;
        const decimal Unary = +(-L);
    }";
    let (_, compilation) = against_corlib!(source);
    let all = u32::MAX;
    let expected = [
        ("L", (1, false, 0, 0, 35)),
        ("N", (27, false, 1_807_003_620, 3_475_376_110, 894_784_853)),
        ("T", (1, false, 0, 0, 25)),
        ("V", (1, false, 0, 0, 15)),
        ("W", (2, true, 0, 0, 25)),
        ("Third", (28, false, 180_700_362, 347_537_611, 89_478_485)),
        (
            "TwoThirds",
            (28, false, 361_400_724, 695_075_222, 178_956_971),
        ),
        ("Trailing", (2, false, 0, 0, 150)),
        ("Product", (2, false, 0, 0, 300)),
        ("NegZero", (0, true, 0, 0, 0)),
        ("NegZeroProduct", (0, true, 0, 0, 0)),
        ("Max", (0, false, all, all, all)),
        ("Min", (0, true, all, all, all)),
        ("NearMax", (0, false, all, all, all)),
        ("Tiny", (28, false, 0, 0, 0)),
        ("Sum", (2, false, 0, 0, 30)),
        ("Rem", (1, false, 0, 0, 15)),
        ("RemNeg", (0, true, 0, 0, 1)),
        ("FromFloat", (1, false, 0, 0, 1)),
        ("FromDouble", (1, false, 0, 0, 1)),
        ("FromBig", (0, false, 6, 2_974_719_873, 792_416_896)),
        ("FromSmall", (5, false, 0, 0, 1)),
        ("FromLost", (0, false, 0, 0, 0)),
        ("FromEnum", (0, false, 0, 0, 201)),
        ("FromChar", (1, false, 0, 0, 975)),
        ("Nested", (2, false, 0, 0, 175)),
        ("Unary", (1, true, 0, 0, 35)),
    ];
    for (name, parts) in expected {
        assert_eq!(
            decimal_at(&compilation, &format!("C.{name}")),
            Some(parts),
            "{name}"
        );
    }
}

#[test]
fn a_decimal_cast_to_another_type_or_compared_is_a_constant_of_it() {
    let (_, compilation) = against_corlib!(
        "class C {
            const decimal L = 3.5m;
            const int ToInt = (int)3.7m;
            const long ToLong = (long)-3.7m;
            const byte ToByte = (byte)255.9m;
            const char ToChar = (char)65.5m;
            const double ToDouble = (double)(1m / 3);
            const float ToFloat = (float)0.1m;
            const bool Less = 1m < 2m;
            const bool Same = 1.0m == 1.00m;
            const bool Other = L != 2.5m;
            const int FromField = (int)(L * 2);
        }"
    );
    let found: Vec<Option<String>> = [
        "ToInt",
        "ToLong",
        "ToByte",
        "ToChar",
        "ToDouble",
        "ToFloat",
        "Less",
        "Same",
        "Other",
        "FromField",
    ]
    .iter()
    .map(|name| constant_at(&compilation, &format!("C.{name}")))
    .collect();
    assert_eq!(
        found,
        [
            "Int32(3)",
            "Int64(-3)",
            "Int32(255)",
            "Char('A')",
            "Double(0.33333333333333337)",
            "Single(0.1)",
            "Boolean(true)",
            "Boolean(true)",
            "Boolean(true)",
            "Int32(7)"
        ]
        .map(|text| Some(text.to_string()))
    );
}

#[test]
fn a_decimal_default_value_that_is_worked_out_is_a_constant() {
    // Neither the cast from a `double` nor the division was folded, and both
    // were taken for something that is not constant (CS1736).
    let (_, compilation) = against_corlib!(
        "enum E { A = 3 }
        class C {
            const decimal L = (decimal)3.5;
            static void D(decimal a = (decimal)3.5, decimal b = 100m / 3, decimal c = 10 / 4m,
                decimal? d = (decimal)1.5f, decimal e = -(decimal)0.25, decimal f = 1m % 3,
                decimal g = (decimal)E.A, decimal h = L * 2, decimal i = decimal.MaxValue,
                decimal j = decimal.MinusOne, int k = (int)3.5m, double l = (double)1.5m,
                bool m = 1m < 2m) { }
        }"
    );
    assert_eq!(errors_in_order(&compilation), Vec::<String>::new());
    // What is no constant still is none.
    let (_, compilation) = against_corlib!(
        "class C { static decimal Four() => 4; static void D(decimal a = Four() / 2) { } }"
    );
    assert_eq!(errors_in_order(&compilation), ["CS1736"]);
}

#[test]
fn a_decimal_constant_that_cannot_be_held_is_an_error_of_its_own() {
    let (_, compilation) = against_corlib!(
        "class C {
            const decimal A = decimal.MaxValue * 2;
            const decimal B = 1m / 0;
            const decimal D = 5m % 0;
            const decimal E = (decimal)1e40;
            const decimal F = (decimal)double.NaN;
            const int G = (int)1e10m;
            const uint H = (uint)-1m;
            const decimal I = decimal.MinValue - 1;
            const int J = unchecked((int)1e10m);
            const decimal Fine = (decimal)1e-30 + 1m / 3;
        }"
    );
    assert_eq!(
        errors_in_order(&compilation),
        [
            "CS0463", "CS0020", "CS0020", "CS0031", "CS0031", "CS0031", "CS0031", "CS0463",
            "CS0031"
        ]
    );
    // A default value that fails to work out says that, and no more.
    let (_, compilation) = against_corlib!(
        "class C { static void D(decimal a = decimal.MaxValue * 2, decimal b = 1m / 0,
            decimal c = (decimal)1e40, int d = (int)1e10m) { } }"
    );
    assert_eq!(
        errors_in_order(&compilation),
        ["CS0463", "CS0020", "CS0031", "CS0031"]
    );
}

#[test]
fn a_const_set_from_a_property_or_a_call_is_cs0133() {
    let (_, compilation) = against_corlib!(
        "class C {
            const nint Max = nint.MaxValue;
            const nuint UMax = nuint.MaxValue;
            const nint Min = nint.MinValue;
            const int Cast = (int)nint.MaxValue;
            static int Q => 1;
            static int M() => 1;
            const int FromProperty = Q;
            const int FromCall = M();
            const nint Five = 5;
            const nint Sum = Five + 1;
            const nint Zero = default;
            const int Size = int.MaxValue / 2;
            const string Text = \"a\" + nameof(Q);
        }"
    );
    assert_eq!(errors_in_order(&compilation), ["CS0133"; 6]);
}
