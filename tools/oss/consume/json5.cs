using System; using Newtonsoft.Json.Linq;
class Program { static void Main() { var o = JObject.Parse("{\"a\": [1, 2, {\"b\": \"c\"}]}"); JToken t = o["a"]; Console.WriteLine(t.Type); } }
