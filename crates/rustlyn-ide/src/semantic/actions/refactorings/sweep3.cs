using System;
using System.Collections.Generic;
using System.Linq;

namespace System
{
    public readonly struct Index
    {
        public Index(int value, bool fromEnd = false) { }
        public int GetOffset(int length) => length;
    }
}

namespace System.Linq
{
    public static class Enumerable
    {
        public static IEnumerable<T> Where<T>(this IEnumerable<T> source, Func<T, bool> test) => source;
        public static IEnumerable<R> Select<T, R>(this IEnumerable<T> source, Func<T, R> map) => null;
        public static int Count<T>(this IEnumerable<T> source) => 0;
        public static int Count<T>(this IEnumerable<T> source, Func<T, bool> test) => 0;
        public static int Sum<T>(this IEnumerable<T> source, Func<T, int> map) => 0;
        public static int Sum(this IEnumerable<int> source) => 0;
        public static List<T> ToList<T>(this IEnumerable<T> source) => null;
    }
}

namespace Shop
{
    public interface IPriced
    {
        double Price();
    }

    public abstract class Product : IPriced
    {
        public abstract double Price();
        public virtual string Label(int width) => "product";
    }

    public class Book : Product
    {
        private readonly string _title;
        public int Pages { get; }

        public Book(string title, int pages)
        {
            _title = title;
            Pages = pages;
        }

        public override double Price() => Pages * 0.5;

        public string Title() => _title;

        public double Discounted(double rate, int copies) => Price() * rate * copies;

        public int Twice(int value) => value * 2;
    }

    public class Point
    {
        public int X { get; }
        public int Y { get; init; }

        public Point(int X, int Y)
        {
            this.X = X;
            this.Y = Y;
        }
    }

    sealed class Numbers
    {
        public const int Limit = 10;
        public static int Clamp(int value) => value > Limit ? Limit : value;
    }

    class Basket
    {
        private readonly List<Book> books = new List<Book>();
        private string owner;
        private Action changed;
        private int[] codes = new int[] { 1, 2, 3 };
        private int size = Numbers.Clamp(4) + 1;

        public void Add(Book book, string label)
        {
            books.Add(book);
            if (owner == null)
            {
                owner = label;
            }
            owner = owner ?? label;
            if (changed != null)
            {
                changed();
            }
        }

        public string Owner(string fallback) => owner != null ? owner : fallback;

        public int Length(Basket other) => other != null ? other.books.Count : 0;

        public string Name(Basket other) => other != null ? other.owner : null;

        private int[] empty = [];

        public void Rename(string label)
        {
            if (label == null) throw new ArgumentNullException(nameof(label));
            owner = label;
        }

        public int Long()
        {
            int n = books.Count(b => b.Pages > 1);
            return n;
        }

        public int Total()
        {
            int total = 0;
            foreach (var book in books)
            {
                total += book.Pages;
            }
            return total;
        }

        public int Big()
        {
            int count = 0;
            foreach (var book in books)
            {
                if (book.Pages > 100)
                {
                    count++;
                }
            }
            return count;
        }

        public void Print()
        {
            foreach (var book in books)
            {
                if (book.Pages > 1)
                {
                    Console.WriteLine(book.Title());
                }
            }
        }

        public int Parse(string text)
        {
            int value;
            if (int.TryParse(text, out value))
            {
                return value;
            }
            return 0;
        }

        public int Kind(object item)
        {
            var book = item as Book;
            if (book != null)
            {
                return book.Pages;
            }
            if (item is Point)
            {
                var point = (Point)item;
                return point.X;
            }
            return !(item is string) ? 1 : 0;
        }

        public bool Check(Point p, int x) => p != null && p.X == 1 && p.Y == 2 || x == 3 || x == 4;

        public bool Same(Basket other) => (object)other == null || size == 0 == true;

        public int Last() => codes[codes.Length - 1];

        public void Grow(int by)
        {
            size = size + by;
            size = size * 2;
        }

        public bool Flag(int a) => a > 1 ? true : false;

        public (int Low, int High) Range() => (1, 9);

        public int Spread()
        {
            var range = Range();
            return range.High - range.Low;
        }

        public int Pair()
        {
            (int A, int B) pair = (A: 1, B: 2);
            var anonymous = new { Name = owner, Count = size };
            return pair.A + anonymous.Count;
        }

        public int Clamped() => Numbers.Clamp(size);

        public double Cost(Book book) => book.Discounted(0.5, 2) + book.Twice(3);

        public string Describe(Book book) => book.Label(10);
    }
}
