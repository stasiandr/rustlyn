using System; using Newtonsoft.Json;
class Person { public string Name { get; set; } public int Age { get; set; } }
class Program { static void Main() { var p = new Person { Name = "Ada", Age = 36 }; string json = JsonConvert.SerializeObject(p); Console.WriteLine(json); var back = JsonConvert.DeserializeObject<Person>(json); Console.WriteLine(back.Name + " " + back.Age); } }
