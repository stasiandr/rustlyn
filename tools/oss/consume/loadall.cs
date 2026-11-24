using System; using System.IO; using System.Linq; using System.Reflection;
class Program { static void Main(string[] args) {
    var path = Environment.GetEnvironmentVariable("LIB_PATH");
    var asm = Assembly.LoadFrom(path);
    Console.WriteLine("assembly: " + asm.GetName().Name);
    Type[] types; int bad = 0;
    try { types = asm.GetTypes(); }
    catch (ReflectionTypeLoadException e) { types = e.Types.Where(t => t != null).ToArray(); foreach (var le in e.LoaderExceptions.Take(12)) { bad++; Console.WriteLine("  " + le.Message.Split('\n')[0]); } }
    int methods = 0, methodFailures = 0;
    foreach (var t in types) { try { methods += t.GetMethods(BindingFlags.DeclaredOnly | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static).Length; } catch (Exception e) { if (methodFailures++ < 5) Console.WriteLine("  " + t.FullName + ": " + e.Message.Split('\n')[0]); } }
    Console.WriteLine($"types loaded: {types.Length}, loader errors: {bad}, methods: {methods}, method failures: {methodFailures}");
} }
