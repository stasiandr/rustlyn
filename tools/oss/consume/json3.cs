using System; using Newtonsoft.Json.Linq;
class Program { static void Main() { var o = JObject.Parse("{\"a\": [1, 2, {\"b\": \"c\"}], \"d\": 1.5}"); JToken t = o["a"]; Console.WriteLine(t.Type); JToken u = t[2]; Console.WriteLine((string)u["b"]); } }
