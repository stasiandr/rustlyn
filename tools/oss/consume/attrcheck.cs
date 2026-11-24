using System; using System.Linq; using System.Reflection; using System.Runtime.CompilerServices;
class Program { static void Main() {
    var asm = Assembly.LoadFrom(Environment.GetEnvironmentVariable("LIB_PATH"));
    Console.WriteLine("asm ext: " + asm.IsDefined(typeof(ExtensionAttribute)));
    foreach (var t in asm.GetTypes().Where(t => t.IsAbstract && t.IsSealed).Take(4)) {
        var ms = t.GetMethods(BindingFlags.Static | BindingFlags.Public);
        Console.WriteLine($"{t.FullName}: type ext={t.IsDefined(typeof(ExtensionAttribute))} methods={ms.Length} ext methods={ms.Count(m => m.IsDefined(typeof(ExtensionAttribute)))}");
    }
} }
