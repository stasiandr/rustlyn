using System; using System.Collections.Generic; using Newtonsoft.Json;
class Program { static void Main() { Console.WriteLine(JsonConvert.SerializeObject(new Dictionary<string, object> { ["k"] = new[] { 1, 2 }, ["n"] = null }, Formatting.Indented)); } }
