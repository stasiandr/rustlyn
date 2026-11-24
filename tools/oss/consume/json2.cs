using System; using Newtonsoft.Json.Linq;
class Program { static void Main() { var o = JObject.Parse("{\"a\": [1, 2, {\"b\": \"c\"}], \"d\": 1.5}"); Console.WriteLine((string)o["a"][2]["b"]); Console.WriteLine(o.Value<double>("d")); } }
