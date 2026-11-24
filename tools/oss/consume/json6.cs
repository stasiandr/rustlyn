using System; using Newtonsoft.Json.Linq;
class Program { static void Main() { var o = JObject.Parse("{\"a\": [1, 2, {\"b\": \"c\"}]}"); JToken u = o["a"][2]; Console.WriteLine((string)u["b"]); } }
