using System; using Humanizer;
class Program { static void Main() {
    Console.WriteLine("PascalCaseInputString".Humanize());
    Console.WriteLine(1234.ToWords());
    Console.WriteLine(42.Ordinalize());
    Console.WriteLine(DateTime.UtcNow.AddHours(-3).Humanize(utcDate: true));
    Console.WriteLine("case".Pluralize() + " " + "boxes".Singularize());
    Console.WriteLine(TimeSpan.FromMinutes(125).Humanize(2));
    Console.WriteLine((1024 * 1024 * 3L).Bytes().Humanize());
} }
