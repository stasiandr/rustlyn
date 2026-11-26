//! Casts that nothing can make (CS0030) between interfaces, delegates,
//! arrays and tuples — and, for each, casts that look close and are fine,
//! which must stay quiet. The types are declared here: the core library
//! these tests bind against is a synthesised one whose `int` and `string`
//! list no interfaces.

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

/// The errors among `wanted` that a file gets, whatever else it is told —
/// that a local is never read, mostly.
fn only(source: &str, wanted: &[&str]) -> Vec<String> {
    codes(source)
        .into_iter()
        .filter(|code| wanted.contains(&code.as_str()))
        .collect()
}

/// Types to cast between, and a method whose parameters are one of each.
fn casting(body: &str) -> String {
    format!(
        "namespace System {{ struct ValueTuple<T1, T2> {{ }} struct ValueTuple<T1, T2, T3> {{ }} }}
         enum E {{ A }} struct S {{ }} struct Other {{ }}
         interface I {{ }} interface J {{ }} interface K : I {{ }}
         interface IG<T> {{ }} interface IV<out T> {{ }}
         class Impl : I {{ }} class NoImpl {{ }} sealed class Sealed {{ }} sealed class SealedI : I {{ }}
         sealed class SealedK : K {{ }} sealed class SealedG : IG<string> {{ }} sealed class SealedV : IV<string> {{ }}
         struct SI : I {{ }} struct SK : K {{ }} enum EI {{ A }}
         class Base : I {{ }} sealed class Heir : Base {{ }}
         struct StructOp {{ public static explicit operator StructOp(I i) => default; }}
         sealed class ArrayOp {{ public static explicit operator ArrayOp(int[] a) => null; }}
         delegate void D1(); delegate void D2(); delegate void D3(int x);
         delegate T DG<T>(); delegate void DC<in T>(T t); delegate void Plain(object o);
         class A {{ }} class B : A {{ }} class C {{ }}
         class Tests<T, U> where T : class {{
             void M(int i, long l, string s, object o, E e, S st, SI si, SK sk, A a, B bb, C cc, Sealed se, SealedI sei, SealedK sk2, SealedG sg, SealedV sv, Heir heir,
                    I it, J jt, K kt, IG<int> igi, IG<string> igs, IV<object> ivo, Impl im, NoImpl ni,
                    D1 d1, D2 d2, D3 d3, DG<int> dgi, DG<string> dgs, DC<string> dcs, DC<object> dco,
                    int[] ia, long[] la, uint[] ua, E[] ea, int?[] nia, string[] sa, object[] oa, A[] aa, B[] ba, C[] ca, I[] ita, Sealed[] sea, Impl[] ima,
                    int[,] ia2, string[,] sa2, int[][] iaa, long[][] laa, string[][] saa, object[][] oaa, S[] sta,
                    ArrayOp aop, T[] ta, U[] ua2,
                    (int, string) tup, (int, int) t2, (int, int, int) t3, (long, long) l2, (string, string) s2, (object, object) o2,
                    (int a, int b) named, (int, int)? nt2, (A, A) aa2, (B, B) bb2, (C, C) cc2, (int, (string, string)) nest, (int, (object, object)) nest2,
                    StructOp sop, T t, U u, dynamic dyn) {{ {body} }}
         }}"
    )
}

/// The one error the cast makes.
fn cast_is_cs0030(cast: &str) {
    assert_eq!(
        only(&casting(&format!("var x = {cast};")), &["CS0030"]),
        ["CS0030"],
        "{cast}"
    );
}

/// No error: the cast is one the language has.
fn cast_is_fine(cast: &str) {
    let found = only(&casting(&format!("var x = {cast};")), &["CS0030"]);
    assert!(found.is_empty(), "{cast}: {found:?}");
}

#[test]
fn an_interface_a_sealed_type_does_not_implement_is_cs0030() {
    assert_eq!(
        diagnose(&casting("var x = (I)se;")),
        ["CS0030 '(I)se': Cannot convert type 'Sealed' to 'I'"]
    );
    assert_eq!(
        diagnose(&casting("var x = (Sealed)it;")),
        ["CS0030 '(Sealed)it': Cannot convert type 'I' to 'Sealed'"]
    );
    for cast in [
        // A sealed class, a struct and an enum have no heirs to add one.
        "(J)sei",
        "(I)se",
        "(Sealed)it",
        "(SealedI)jt",
        "(J)st",
        "(I)st",
        "(S)it",
        "(J)si",
        "(SI)jt",
        // A struct that implements an interface does not implement another.
        "(J)sk",
        // What a heir adds is a heir's: a sealed class gets only what its
        // bases have.
        "(J)heir",
        "(Heir)jt",
        // A generic interface of a family the class implements none of.
        "(IG<int>)sei",
        "(IG<int>)si",
        // Through a nullable.
        "(J)(S?)null",
    ] {
        cast_is_cs0030(cast);
    }
}

#[test]
fn an_interface_a_type_may_implement_is_not_cs0030() {
    for cast in [
        // Implemented, directly, through a base interface and through a base
        // class.
        "(I)sei",
        "(SealedI)it",
        "(I)si",
        "(SI)it",
        "(I)sk",
        "(K)sk",
        "(I)sk2",
        "(SealedK)it",
        "(I)heir",
        "(Heir)it",
        "(Base)it",
        // A class that is not sealed may have an heir that implements it.
        "(J)im",
        "(J)ni",
        "(J)a",
        "(A)jt",
        "(NoImpl)it",
        "(I)o",
        "(J)o",
        // Two interfaces: one type can implement both.
        "(J)it",
        "(K)it",
        "(I)kt",
        // Generic interfaces convert by variance, and an instance of the
        // family may.
        "(IG<int>)sg",
        "(IG<string>)sg",
        "(SealedG)igi",
        "(SealedG)igs",
        "(IV<object>)sv",
        "(IV<int>)sv",
        "(SealedV)ivo",
        // An operator between an interface and the struct.
        "(StructOp)it",
        "(StructOp)sei",
        // Type parameters, `dynamic` and null.
        "(I)t",
        "(T)it",
        "(I)dyn",
        "(Sealed)dyn",
    ] {
        cast_is_fine(cast);
    }
}

#[test]
fn the_types_of_the_synthesised_core_library_have_no_interfaces_to_judge_by() {
    // The `int` and the `string` of these tests list none, so a cast of one
    // to an interface it has in the real library cannot be called wrong.
    // `System.IComparable` is declared by the file, as a user type would be:
    // nothing says `int` does not implement it.
    // Nor does an enum of the file, whose `Enum` lists none here.
    let source = "interface IComparable { } enum E { A }
        class C { void M(int i, string s, long l, E e, IComparable c) { var a = (IComparable)i; var b = (IComparable)s; var d = (IComparable)l; var f = (IComparable)e; var g = (E)c; } }";
    assert!(only(source, &["CS0030"]).is_empty());
}

#[test]
fn a_delegate_cast_to_another_delegate_is_cs0030() {
    assert_eq!(
        diagnose(&casting("var x = (D2)d1;")),
        ["CS0030 '(D2)d1': Cannot convert type 'D1' to 'D2'"]
    );
    for cast in [
        // Two declarations, and one that is generic or not.
        "(D1)d2",
        "(D3)d1",
        "(D1)d3",
        "(DG<int>)d1",
        "(D1)dgi",
        "(DC<string>)d3",
        // A delegate and a class, a struct, an enum or an array.
        "(A)d1",
        "(D1)a",
        "(S)d1",
        "(D1)st",
        "(E)d1",
        "(D1)ia",
        "(int[])d1",
        "(D1)s",
    ] {
        cast_is_cs0030(cast);
    }
}

#[test]
fn a_delegate_cast_that_may_convert_is_not_cs0030() {
    for cast in [
        // `object`.
        "(D1)o",
        "(object)d1",
        // One generic delegate converts to itself by variance, both ways.
        "(DC<object>)dcs",
        "(DC<string>)dco",
        "(DG<string>)dgs",
        // Lambdas, method groups and `null` take the delegate they are cast to.
        "(D1)(() => { })",
        "(D1)null",
        "(D1)dyn",
        // A delegate reaches an interface it may implement.
        "(I)d1",
    ] {
        cast_is_fine(cast);
    }
}

#[test]
fn an_array_cast_nothing_converts_is_cs0030() {
    assert_eq!(
        diagnose(&casting("var x = (long[])ia;")),
        ["CS0030 '(long[])ia': Cannot convert type 'int[]' to 'long[]'"]
    );
    for cast in [
        // Elements that are value types must be the one type.
        "(long[])ia",
        "(int[])la",
        "(uint[])ia",
        "(E[])ia",
        "(int[])ea",
        "(int?[])ia",
        "(int[])nia",
        "(object[])ia",
        "(int[])oa",
        "(S[])ia",
        "(string[])ia",
        "(int[])sa",
        // Ranks.
        "(int[,])ia",
        "(int[])ia2",
        "(string[])sa2",
        "(string[,])sa",
        // Arrays of arrays, down to their elements.
        "(long[][])iaa",
        "(int[][])laa",
        "(string[][])iaa",
        "(object[][])iaa",
        // Elements that are reference types nothing converts between.
        "(A[])ca",
        "(C[])aa",
        "(string[])aa",
        "(Sealed[])ita",
        "(I[])sea",
        // An array and what is not `object` or `Array`.
        "(A)ia",
        "(int[])a",
        "(string)ia",
        "(int[])s",
        "(S)ia",
        "(int[])st",
        "(int)ia",
        "(E)ia",
        "(Sealed)ia",
    ] {
        cast_is_cs0030(cast);
    }
}

#[test]
fn an_array_cast_that_may_convert_is_not_cs0030() {
    for cast in [
        // Reference elements convert as they would on their own.
        "(object[])sa",
        "(string[])oa",
        "(A[])ba",
        "(B[])aa",
        "(I[])aa",
        "(A[])ita",
        "(I[])ima",
        "(Impl[])ita",
        "(object[][])saa",
        "(string[][])oaa",
        "(object[,])sa2",
        "(string[,])(object[,])sa2",
        // `object`, and back.
        "(object)ia",
        "(int[])o",
        "(Array)ia",
        "(int[])(object)la",
        // Arrays and interfaces are not judged.
        "(I)ia",
        "(J)sa",
        "(I[])(object)ia",
        // Identical elements, and `null`.
        "(int[])ia",
        "(S[])sta",
        "(int[])null",
        // An operator from the array.
        "(ArrayOp)ia",
        "(int[])aop",
        // Type parameters and `dynamic`.
        "(T[])oa",
        "(object[])ta",
        "(A[])ta",
        "(U[])ia",
        "(int[])dyn",
        "(T[])aa",
    ] {
        cast_is_fine(cast);
    }
}

#[test]
fn a_tuple_cast_nothing_converts_is_cs0030() {
    // The synthesised core library has to declare the `ValueTuple`s a tuple
    // is made of; where it does not, the cast is not judged and this finds
    // nothing.
    for cast in [
        // A tuple is not a number, a class or an enum.
        "(int)tup",
        "(string)tup",
        "(A)tup",
        "(S)tup",
        "(E)tup",
        "(D1)tup",
        "(int[])tup",
        "(int)nt2",
        // Another number of elements.
        "((int, int, int))t2",
        "((int, int))t3",
        "(System.ValueTuple<int, int, int>)t2",
        // Elements that nothing converts.
        "((string, string))t2",
        "((int, int))s2",
        "((int, string))t2",
        "((A, A))cc2",
        "((C, C))aa2",
        "((int, (A, A)))nest",
        "((int, (int, string)))nest",
    ] {
        cast_is_cs0030(cast);
    }
    // One error on the cast, not one for each element that fails.
    assert_eq!(
        only(&casting("var x = ((string, string))t2;"), &["CS0030"]),
        ["CS0030"]
    );
}

#[test]
fn a_tuple_cast_that_may_convert_is_not_cs0030() {
    for cast in [
        // Element by element, with the conversions the elements have.
        "((long, long))t2",
        "((int, int))l2",
        "((object, object))t2",
        "((int, int))o2",
        "((A, A))bb2",
        "((B, B))aa2",
        "((int a, int b))t2",
        "((int, int))named",
        "((int, (object, object)))nest",
        "((int, (string, string)))nest2",
        "((int, int)?)t2",
        "((int, int))nt2",
        "((long, long)?)t2",
        // What every value type reaches.
        "(object)tup",
        "((int, string))o",
        "((int, string))(object)tup",
        // A tuple of a type that is not understood.
        "((T, T))t2",
        "((int, int))dyn",
    ] {
        cast_is_fine(cast);
    }
}

#[test]
fn an_operator_makes_a_cast_that_would_be_cs0030_legal() {
    let source = "
        class FromTuple { public static explicit operator FromTuple((int, int) t) => null; }
        sealed class S { public static implicit operator S(int[] a) => null; }
        class C { void M((int, int) t, int[] a) {
            var x = (FromTuple)t;
            var y = (S)a;
            var z = (int[])null;
        } }";
    assert!(only(source, &["CS0030"]).is_empty());
}
