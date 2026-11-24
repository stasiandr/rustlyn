using System; using Newtonsoft.Json.Linq;
class Program { static void Main() { var o = JObject.Parse("{\"b\": \"c\"}"); JToken v = o["b"]; string s = (string)v; Console.WriteLine(s); } }
