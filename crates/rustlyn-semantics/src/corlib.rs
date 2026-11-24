//! A core library synthesised as source.
//!
//! A real compilation reads `System.Object` and friends out of a reference
//! assembly. Rustlyn has no metadata reader, so it compiles a small core
//! library from source instead: the same declaration pass, the same symbols,
//! no special cases anywhere else. It is a stand-in, not a shim — the types
//! below are only as complete as the rest of the compiler needs them to be.

use rustlyn_syntax::SyntaxKind;

/// The types the language itself knows about, which is what a keyword like
/// `int` has to resolve to.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum SpecialType {
    Object,
    Void,
    Boolean,
    Char,
    SByte,
    Byte,
    Int16,
    UInt16,
    Int32,
    UInt32,
    Int64,
    UInt64,
    Single,
    Double,
    Decimal,
    String,
}

impl SpecialType {
    /// The name the type has in metadata.
    #[must_use]
    pub const fn metadata_name(self) -> &'static str {
        match self {
            Self::Object => "System.Object",
            Self::Void => "System.Void",
            Self::Boolean => "System.Boolean",
            Self::Char => "System.Char",
            Self::SByte => "System.SByte",
            Self::Byte => "System.Byte",
            Self::Int16 => "System.Int16",
            Self::UInt16 => "System.UInt16",
            Self::Int32 => "System.Int32",
            Self::UInt32 => "System.UInt32",
            Self::Int64 => "System.Int64",
            Self::UInt64 => "System.UInt64",
            Self::Single => "System.Single",
            Self::Double => "System.Double",
            Self::Decimal => "System.Decimal",
            Self::String => "System.String",
        }
    }

    /// The keyword that spells this type, if one does.
    #[must_use]
    pub const fn keyword(self) -> &'static str {
        match self {
            Self::Object => "object",
            Self::Void => "void",
            Self::Boolean => "bool",
            Self::Char => "char",
            Self::SByte => "sbyte",
            Self::Byte => "byte",
            Self::Int16 => "short",
            Self::UInt16 => "ushort",
            Self::Int32 => "int",
            Self::UInt32 => "uint",
            Self::Int64 => "long",
            Self::UInt64 => "ulong",
            Self::Single => "float",
            Self::Double => "double",
            Self::Decimal => "decimal",
            Self::String => "string",
        }
    }

    /// The type a predefined-type keyword names.
    #[must_use]
    pub const fn from_keyword(kind: SyntaxKind) -> Option<Self> {
        Some(match kind {
            SyntaxKind::ObjectKeyword => Self::Object,
            SyntaxKind::VoidKeyword => Self::Void,
            SyntaxKind::BoolKeyword => Self::Boolean,
            SyntaxKind::CharKeyword => Self::Char,
            SyntaxKind::SByteKeyword => Self::SByte,
            SyntaxKind::ByteKeyword => Self::Byte,
            SyntaxKind::ShortKeyword => Self::Int16,
            SyntaxKind::UShortKeyword => Self::UInt16,
            SyntaxKind::IntKeyword => Self::Int32,
            SyntaxKind::UIntKeyword => Self::UInt32,
            SyntaxKind::LongKeyword => Self::Int64,
            SyntaxKind::ULongKeyword => Self::UInt64,
            SyntaxKind::FloatKeyword => Self::Single,
            SyntaxKind::DoubleKeyword => Self::Double,
            SyntaxKind::DecimalKeyword => Self::Decimal,
            SyntaxKind::StringKeyword => Self::String,
            _ => return None,
        })
    }

    /// Whether values of this type are numbers.
    #[must_use]
    pub const fn is_numeric(self) -> bool {
        matches!(
            self,
            Self::SByte
                | Self::Byte
                | Self::Int16
                | Self::UInt16
                | Self::Int32
                | Self::UInt32
                | Self::Int64
                | Self::UInt64
                | Self::Single
                | Self::Double
                | Self::Decimal
                | Self::Char
        )
    }

    /// Every special type, so a compilation can look them all up at once.
    pub const ALL: &'static [Self] = &[
        Self::Object,
        Self::Void,
        Self::Boolean,
        Self::Char,
        Self::SByte,
        Self::Byte,
        Self::Int16,
        Self::UInt16,
        Self::Int32,
        Self::UInt32,
        Self::Int64,
        Self::UInt64,
        Self::Single,
        Self::Double,
        Self::Decimal,
        Self::String,
    ];
}

/// The source of the synthesised core library.
pub(crate) const CORLIB_SOURCE: &str = r#"
namespace System
{
    public class Object
    {
        public Object() { }
        public virtual string ToString() { return null; }
        public virtual bool Equals(object other) { return false; }
        public virtual int GetHashCode() { return 0; }
        public Type GetType() { return null; }
    }

    public struct Void { }
    public abstract class ValueType : Object { }
    public abstract class Enum : ValueType { }
    public abstract class Array : Object { public int Length { get { return 0; } } }
    public abstract class Delegate : Object { }
    public abstract class MulticastDelegate : Delegate { }
    public class Type : Object
    {
        public string Name { get { return null; } }
        public static bool operator ==(Type left, Type right) { return false; }
        public static bool operator !=(Type left, Type right) { return false; }
    }
    public interface IEquatable<T> { bool Equals(T other); }
    public class Attribute : Object { }
    public sealed class FlagsAttribute : Attribute { }

    public struct Boolean : ValueType { }
    public struct Char : ValueType { }
    public struct SByte : ValueType { }
    public struct Byte : ValueType { }
    public struct Int16 : ValueType { }
    public struct UInt16 : ValueType { }
    public struct Int32 : ValueType
    {
        public static bool TryParse(string text, out int result) { result = 0; return false; }
        public static int Parse(string text) { return 0; }
    }
    public struct UInt32 : ValueType { }
    public struct Int64 : ValueType { }
    public struct UInt64 : ValueType { }
    public struct Single : ValueType { }
    public struct Double : ValueType
    {
        public static bool TryParse(string text, out double result) { result = 0; return false; }
        public static double Parse(string text) { return 0; }
    }
    public struct Decimal : ValueType { }
    public struct IntPtr : ValueType { }
    public struct UIntPtr : ValueType { }
    public struct Nullable<T> : ValueType
    {
        public bool HasValue { get { return false; } }
        public T Value { get { return default; } }
    }

    public sealed class String : Object
    {
        public int Length { get { return 0; } }
        public char this[int index] { get { return default; } }
        public static string Concat(string a, string b) { return null; }
        public string Substring(int startIndex) { return null; }
        public bool Contains(string value) { return false; }
        public string Trim() { return null; }
    }

    public class Exception : Object
    {
        public Exception() { }
        public Exception(string message) { }
        public string Message { get; }
    }

    public class InvalidOperationException : Exception
    {
        public InvalidOperationException() { }
        public InvalidOperationException(string message) { }
    }
    public class ArgumentException : Exception
    {
        public ArgumentException() { }
        public ArgumentException(string message) { }
    }
    public class NotSupportedException : Exception
    {
        public NotSupportedException() { }
        public NotSupportedException(string message) { }
    }
    public class ArgumentNullException : ArgumentException
    {
        public ArgumentNullException() { }
        public ArgumentNullException(string paramName) { }
    }
    public class IndexOutOfRangeException : Exception
    {
        public IndexOutOfRangeException() { }
        public IndexOutOfRangeException(string message) { }
    }
    public class DivideByZeroException : Exception
    {
        public DivideByZeroException() { }
        public DivideByZeroException(string message) { }
    }

    public interface IDisposable { void Dispose(); }

    public static class Console
    {
        public static void Write(string value) { }
        public static void Write(char value) { }
        public static void Write(int value) { }
        public static void Write(long value) { }
        public static void Write(uint value) { }
        public static void Write(ulong value) { }
        public static void Write(double value) { }
        public static void Write(bool value) { }
        public static void Write(object value) { }
        public static void WriteLine() { }
        public static void WriteLine(string value) { }
        public static void WriteLine(char value) { }
        public static void WriteLine(int value) { }
        public static void WriteLine(long value) { }
        public static void WriteLine(uint value) { }
        public static void WriteLine(ulong value) { }
        public static void WriteLine(double value) { }
        public static void WriteLine(bool value) { }
        public static void WriteLine(object value) { }
        public static string ReadLine() { return null; }
    }

    public delegate void Action();
    public delegate void Action<T>(T arg);
    public delegate void Action<T1, T2>(T1 arg1, T2 arg2);
    public delegate TResult Func<TResult>();
    public delegate TResult Func<T, TResult>(T arg);
    public delegate TResult Func<T1, T2, TResult>(T1 arg1, T2 arg2);
    public delegate bool Predicate<T>(T obj);

    public static class Math
    {
        public const double PI = 3.14159265358979;
        public const double E = 2.71828182845905;
        public static int Abs(int value) { return 0; }
        public static double Abs(double value) { return 0; }
        public static int Max(int a, int b) { return 0; }
        public static int Min(int a, int b) { return 0; }
    }
}

namespace System.Diagnostics
{
    public sealed class ConditionalAttribute : System.Attribute
    {
        public ConditionalAttribute(string conditionString) { }
    }
}

namespace System.Text
{
    public sealed class StringBuilder
    {
        public StringBuilder() { }
        public StringBuilder Append(string value) { return this; }
        public StringBuilder Append(char value) { return this; }
        public StringBuilder Append(object value) { return this; }
    }
}

namespace System.Collections
{
    public interface IEnumerator { object Current { get; } bool MoveNext(); }
    public interface IEnumerable { IEnumerator GetEnumerator(); }
}

namespace System.Collections.Generic
{
    public interface IEnumerator<T> : System.Collections.IEnumerator, System.IDisposable { T Current { get; } }
    public interface IEnumerable<T> : System.Collections.IEnumerable { IEnumerator<T> GetEnumerator(); }

    public class List<T> : IEnumerable<T>
    {
        public int Count { get { return 0; } }
        public void Add(T item) { }
        public T this[int index] { get { return default; } set { } }
    }

    public class Dictionary<TKey, TValue>
    {
        public int Count { get { return 0; } }
        public TValue this[TKey key] { get { return default; } set { } }
        public void Add(TKey key, TValue value) { }
    }
}
"#;
