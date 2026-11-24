using System; using System.Linq; using ExtLib; class P { static void Main() { Console.WriteLine("hi".Shout()); Console.WriteLine(Enumerable.Range(1, 7).Batch(3).Count()); } }
