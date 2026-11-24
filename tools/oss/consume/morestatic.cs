using System; using System.Linq; class P { static void Main() { Console.WriteLine(MoreLinq.MoreEnumerable.Batch(Enumerable.Range(1, 7), 3).Count()); } }
