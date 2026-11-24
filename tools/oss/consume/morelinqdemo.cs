using System; using System.Linq; using MoreLinq;
class Program { static void Main() {
    var xs = Enumerable.Range(1, 10);
    Console.WriteLine(string.Join(" | ", xs.Batch(3).Select(b => string.Join(",", b))));
    Console.WriteLine(string.Join(",", xs.Pairwise((a, b) => a * b)));
    Console.WriteLine(string.Join(",", xs.TakeEvery(3)));
    Console.WriteLine(xs.Maxima(x => x % 4).First());
    Console.WriteLine(string.Join(",", xs.Interleave(new[] { 100, 200 })));
    Console.WriteLine(string.Join(",", "abc".Cartesian("xy", (a, b) => $"{a}{b}")));
    Console.WriteLine(string.Join(";", xs.GroupAdjacent(x => x / 4).Select(g => g.Key + ":" + g.Count())));
} }
