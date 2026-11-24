using System;
using System.Collections.Generic;

namespace Demo
{
    public enum Color { Red, Green = 5, Blue }

    public class Point
    {
        public int X;
        public int Y { get; set; }
        public const int Max = 100;
        private readonly List<string> names = new List<string>();
        public static int Count;

        public Point(int x, int y) { X = x; Y = y; }

        public int Sum(int[] items)
        {
            int total = 0;
            for (int i = 0; i < items.Length; i++)
            {
                total += items[i];
            }
            foreach (var n in names)
            {
                if (n == null || n.Length > 3 && n[0] == 'a')
                    continue;
                total += n.Length;
            }
            return total;
        }

        public string Describe(object o)
        {
            if (o is string s) return "string " + s;
            switch (X)
            {
                case 0: return "zero";
                case 1: case 2: return "small";
                default: break;
            }
            string result = X > Y ? "wide" : "tall";
            try
            {
                result += o.ToString();
            }
            catch (InvalidOperationException e) when (e.Message.Length > 0)
            {
                Console.WriteLine(e);
            }
            catch (Exception)
            {
                throw;
            }
            finally
            {
                Count++;
            }
            return result ?? "none";
        }

        public static bool Check(Color c, bool flag, double d)
        {
            while (d > 1.0) { d /= 2; if (flag) break; }
            do { d++; } while (d < 0.5);
            return c == Color.Green && !flag || d != 0;
        }

        public T First<T>(IEnumerable<T> xs) where T : class
        {
            using (var e = xs.GetEnumerator())
            {
                if (e.MoveNext()) return e.Current;
            }
            return null;
        }

        public override string ToString() => $"({X}, {Y})";
        public Func<int, int> Adder(int k) => v => v + k + X;
    }
    static class Program
    {
        static void Main() { var p = new Point(1, 2) { X = 3 }; int[] a = { 1, 2, 3 }; Console.WriteLine(p.Sum(a)); Console.WriteLine(p.Describe(p)); }
    }
}
