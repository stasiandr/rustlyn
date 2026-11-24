using System; using System.Collections.Generic; using Newtonsoft.Json; using Newtonsoft.Json.Linq;
class Person { [JsonProperty("full_name")] public string Name { get; set; } public int Age { get; set; } [JsonIgnore] public string Secret { get; set; } public List<string> Tags { get; set; } }
class Program { static void Main() {
    var p = new Person { Name = "Ada", Age = 36, Secret = "x", Tags = new List<string> { "math", "code" } };
    string json = JsonConvert.SerializeObject(p);
    Console.WriteLine(json);
    var back = JsonConvert.DeserializeObject<Person>(json);
    Console.WriteLine($"{back.Name} {back.Age} {back.Tags.Count}");
    var o = JObject.Parse("{\"a\": [1, 2, {\"b\": \"c\"}], \"d\": 1.5}");
    Console.WriteLine(o["a"][2]["b"] + " " + o.Value<double>("d"));
    Console.WriteLine(JsonConvert.SerializeObject(new Dictionary<string, object> { ["k"] = new[] { 1, 2 }, ["n"] = null }, Formatting.Indented));
} }
