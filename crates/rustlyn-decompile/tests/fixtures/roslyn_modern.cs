// Built by csc twice, as roslyn_modern.dll with -optimize and as
// roslyn_modern_debug.dll without; see tests/decompile.rs.
using System;
using System.Collections.Generic;
using System.Runtime.CompilerServices;
using System.Threading;
using System.Threading.Tasks;

namespace Modern
{
    public record Point(int X, int Y)
    {
        public double Length => Math.Sqrt(X * X + Y * Y);
    }

    public class Person(string name, int age)
    {
        public int Age { get; } = age;
        public override string ToString() => $"{name} ({age})";
    }

    [AttributeUsage(AttributeTargets.Class | AttributeTargets.Field)]
    public class TagAttribute : Attribute
    {
        public TagAttribute(string name) { Name = name; }
        public string Name { get; }
        public int Level { get; set; }
    }

    [Tag("settings", Level = 2)]
    public class Settings
    {
        [Obsolete("use Limit")] public int Old;
        [NonSerialized] public int Cache;
        public required string Title { get; init; }
        public const decimal Rate = 0.25m;
    }

    public class Handle
    {
        public static bool operator ==(Handle a, Handle b) => ReferenceEquals(a, b);
        public static bool operator !=(Handle a, Handle b) => !(a == b);
        public override bool Equals(object o) => ReferenceEquals(this, o);
        public override int GetHashCode() => 0;
    }

    public static class Samples
    {
        public static int Lookup(string s)
        {
            switch (s)
            {
                case "alpha": return 1;
                case "beta": return 2;
                case "gamma": return 3;
                case "delta": return 4;
                case "epsilon": return 5;
                case "zeta": return 6;
                case "eta": return 7;
                default: return 0;
            }
        }

        public static void Act(string command, int x)
        {
            int y = 0;
            switch (command)
            {
                case "add": y = x + 1; break;
                case "sub":
                case "minus": y = x - 1; break;
                case "noop": return;
                default: Console.WriteLine("unknown " + command); break;
            }
            Console.WriteLine(y);
        }

        public static string Classify(object o) => o switch
        {
            null => "null",
            int i when i > 100 => "big",
            int i => "int " + i,
            string s => $"string of {s.Length}",
            Point { X: 0, Y: 0 } => "origin",
            _ => "other",
        };

        public static bool Same(Handle a, Handle b) => (object)a == b;

        public static bool Missing(Handle h) => h is null;

        public static Point Moved(Point p) => p with { Y = 5 };

        public static T Make<T>() where T : new() => new T();

        public static int Shift(int a) => a >>> 3;

        public static int Bump(ref int a)
        {
            ref int r = ref a;
            r++;
            return r;
        }

        public static async Task<int> Sum(IAsyncEnumerable<int> xs)
        {
            int total = 0;
            await foreach (var x in xs)
                total += x;
            return total;
        }

        public static async Task Finally(Task t)
        {
            try { await t; }
            finally { await Task.Delay(1); }
        }

        public static async IAsyncEnumerable<int> Count(int n, [EnumeratorCancellation] CancellationToken ct = default)
        {
            for (int i = 0; i < n; i++)
            {
                await Task.Delay(1, ct);
                yield return i;
            }
        }

        public static unsafe int Pointers(int* p, int n, string s)
        {
            int total = 0;
            for (int i = 0; i < n; i++)
                total += p[i];
            fixed (char* c = s)
                total += c[0];
            return total;
        }
    }

    public enum Mode { Cbc = 1, Ecb = 2, Ofb = 3, Cfb = 4 }

    public class Searches
    {
        private string _text = "";
        private int _pos;

        public static string Sparse(int n)
        {
            switch (n)
            {
                case 1: return "one";
                case 10: return "ten";
                case 100: return "hundred";
                case 1000: return "thousand";
                case 10000: return "ten thousand";
                default: return "many";
            }
        }

        public static int Pick(int size, int feedback, Mode mode) =>
            (size, mode) switch
            {
                (128, Mode.Cbc) => 1,
                (128, Mode.Ecb) => 2,
                (128, Mode.Cfb) when feedback == 8 => 3,
                (192, Mode.Cbc) => 4,
                (192, Mode.Ecb) => 5,
                (256, Mode.Cbc) => 6,
                _ => throw new ArgumentException(),
            };

        public int Digits()
        {
            int value = 0;
            int digit;
            while (_pos < _text.Length && (uint)(digit = _text[_pos] - '0') <= 9)
            {
                _pos++;
                value = value * 10 + digit;
            }
            return value;
        }
    }

    public static class LocalFunctions
    {
        public static int Twice(int a)
        {
            int b = a * 2;
            return Add(1) + Again();
            int Add(int x) => x + b;
            int Again() => Add(b) * 2;
        }

        public static string Copy(string text)
        {
            char[] buffer = new char[2];
            int written = 0;
            foreach (char c in text)
                Put(c);
            return new string(buffer, 0, written);

            void Put(char c)
            {
                if (written == buffer.Length)
                    Grow();
                buffer[written++] = c;
            }

            void Grow() => Array.Resize(ref buffer, buffer.Length * 2);
        }
    }

    public static class NestedLambdas
    {
        public static Func<int, Func<string, int>> Curry(int bias)
        {
            Func<int, Func<string, int>> make = null;
            make = n => text => text.Length + n + bias + (make == null ? 0 : 1);
            return make;
        }

        public static U Map<T, U>(Func<T, U> f, T x)
        {
            return Go();
            U Go() => f(x);
        }
    }

    public struct Bits
    {
        private uint _data;
        public Bits(int data) { _data = unchecked((uint)data); }
        public bool this[int bit]
        {
            get => (_data & (uint)bit) == (uint)bit;
            set { if (value) _data |= (uint)bit; else _data &= ~(uint)bit; }
        }
        public int Data => unchecked((int)_data);
    }

    public abstract class Hidden : System.Collections.IEnumerable
    {
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => null;
        public int GetEnumerator() => 0;
    }

    public class Derived : Hidden
    {
        public Derived(Derived other) : base() { Inner = (other as System.Collections.IEnumerable)?.GetEnumerator(); }
        public System.Collections.IEnumerator Inner;
        public System.Collections.IEnumerator Walk() => ((System.Collections.IEnumerable)this).GetEnumerator();
    }

    public enum Kind { A, B, C, D, E, F, G, H, I, J }

    public static class SharedTails
    {
        static void W(string s) => Console.WriteLine(s);

        public static void Lift(Kind k, bool same, int n)
        {
            switch (k)
            {
                default:
                case Kind.C: case Kind.D: case Kind.E: case Kind.F:
                    {
                        for (int i = 0; i < n; i++) W("loop" + i);
                        W("tail");
                        break;
                    }
                case Kind.A: case Kind.B:
                    {
                        if (same) goto default;
                        for (int i = 0; i < n; i++) W("d" + i);
                        W("eq");
                        break;
                    }
            }
        }

        public static int Next(string time, int index)
        {
            bool quoted = false;
            while (index < time.Length)
            {
                char c = time[index];
                switch (c)
                {
                    case '\\':
                        index++;
                        break;
                    case '\'':
                        quoted = !quoted;
                        break;
                    case 'H':
                    case 'h':
                    case 'm':
                    case 't':
                        if (!quoted) return index;
                        break;
                }
                index++;
            }
            return -1;
        }
    }

    public unsafe struct FixedBits
    {
        private fixed uint _words[4];
        public void Set(int i) { _words[i >> 5] |= 1u << (i & 31); }
        public bool Get(int i) => (_words[i >> 5] & (1u << (i & 31))) != 0;
    }

    public delegate bool TryParser(string s, out int value);

    public class Recompiled
    {
        public static readonly int[,] Grid = { { 1, 2, 3 }, { 4, 5, 6 } };
        private Holder _holder;
        public ref readonly Holder Current => ref _holder;

        public int Read()
        {
            ref readonly Holder h = ref Current;
            return h.Value + h.Value;
        }

        public static bool Same(List<int> a, List<string> b)
        {
            return Equal(a, a) && Equal(b, b);
            static bool Equal<TValue>(List<TValue> x, List<TValue> y) => x.Count == y.Count;
        }

        public static TryParser Parser() => (string s, out int value) => int.TryParse(s, out value);

        public static int Total(params int[] xs) => Total((IEnumerable<int>)xs);
        public static int Total(IEnumerable<int> xs)
        {
            int sum = 0;
            foreach (int x in xs) sum += x;
            return sum;
        }

        public static uint Flag(bool b) => b ? 1u : 0u;
    }

    public struct Holder { public int Value; }

    public struct Slot { public long Ptr; public int Size; }

    public static class Wide
    {
        public static long Bit(int t) => 1L << t;
        public static bool Has(ulong mask, int t) => (mask & (1UL << t)) != 0;
    }

    public static class Anonymous
    {
        public static int Pairs(List<string> names)
        {
            var rows = names.ConvertAll(n => new { n, Size = n.Length });
            var all = new[] { new { Size = 1 } };
            return rows.Count + all[0].Size;
        }
    }

    public static unsafe class Slots
    {
        public static void Fill(Slot* d, int a, int b)
        {
            Slot x = default;
            x.Ptr = a;
            x.Size = 4;
            d[0] = x;
            x = default;
            x.Ptr = b;
            x.Size = 8;
            d[1] = x;
        }
    }

    public class Generic<T>
    {
        private enum Kind { None, Some }
        private Kind _kind;
        public bool IsSome => _kind == Kind.Some;
    }
}
