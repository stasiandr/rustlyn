using System; using Newtonsoft.Json.Linq;
class Program { static void Main() { var o = JObject.Parse("{\"d\": 1.5}"); Console.WriteLine(o.Value<double>("d")); } }
