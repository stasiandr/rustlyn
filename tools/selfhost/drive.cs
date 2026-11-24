// drive.cs — drives a Roslyn.dll built by rustlyn through reflection.
//
//   dotnet drive.dll Program.cs [--roslyn Roslyn.dll] [--out Program.dll]
//       compiles one file against the runtime's own assemblies, runs
//       C.M(41), C.Greet("roslyn") and C.Run() where the program has them
//   dotnet drive.dll files.txt "DEF1;DEF2" [--emit] [--roslyn Roslyn.dll] [--out Corpus.dll]
//       [--resources-from Other.dll] [--nowarn ID;ID]
//       parses every file listed, reports the diagnostics by severity and
//       id, and with --emit writes the assembly, copying the manifest
//       resources of --resources-from (or of the Roslyn used) into it
//
// Everything goes through reflection because the Roslyn to drive is only
// known at run time, and because a driver that referenced Roslyn's types
// would have to be compiled against the very assembly it tests.
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Reflection;
using System.Threading;

static class Program
{
    static void Report(Exception e)
    {
        var current = e;
        int depth = 0;
        while (current != null && depth < 8)
        {
            Console.WriteLine(new string(' ', depth * 2) + current.GetType().FullName + ": " + current.Message);
            var frames = new StackTrace(current, false).GetFrames();
            for (int i = 0; i < frames.Length && i < 20; i++)
            {
                var method = frames[i].GetMethod();
                var owner = method?.DeclaringType?.FullName ?? "?";
                Console.WriteLine(new string(' ', depth * 2) + "   at " + owner + "::" + method?.Name + " IL_" + frames[i].GetILOffset().ToString("x4"));
            }
            current = current.InnerException;
            depth++;
        }
    }

    static MethodInfo Find(Type type, string name, int arity, Type first)
    {
        foreach (var m in type.GetMethods(BindingFlags.Public | BindingFlags.Static | BindingFlags.Instance))
        {
            if (m.Name != name) continue;
            var ps = m.GetParameters();
            if (ps.Length != arity) continue;
            if (first != null && ps[0].ParameterType != first) continue;
            return m;
        }
        return null;
    }

    static object[] Defaults(MethodInfo m, params object[] given)
    {
        var ps = m.GetParameters();
        var arguments = new object[ps.Length];
        for (int i = 0; i < ps.Length; i++)
        {
            if (i < given.Length) arguments[i] = given[i];
            else if (ps[i].ParameterType == typeof(CancellationToken)) arguments[i] = default(CancellationToken);
            else arguments[i] = ps[i].HasDefaultValue ? ps[i].DefaultValue : null;
        }
        return arguments;
    }

    static object Invoke(MethodInfo m, object receiver, object[] arguments)
    {
        try { return m.Invoke(receiver, arguments); }
        catch (TargetInvocationException e) when (e.InnerException != null)
        {
            System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(e.InnerException).Throw();
            throw;
        }
    }

    static string Option(string[] args, string name, string fallback)
    {
        int at = Array.IndexOf(args, name);
        return at >= 0 && at + 1 < args.Length ? args[at + 1] : fallback;
    }

    static string Describe(object diagnostic)
    {
        try { return diagnostic.ToString(); }
        catch (Exception inner)
        {
            var id = diagnostic.GetType().GetProperty("Id")?.GetValue(diagnostic);
            var location = diagnostic.GetType().GetProperty("Location")?.GetValue(diagnostic);
            return id + " at " + location + " <" + inner.GetType().Name + ": " + inner.Message + ">";
        }
    }

    static Assembly roslyn;
    static string nowarn = "";

    static object ParseOptions(string defines)
    {
        var parseOptionsType = roslyn.GetType("Microsoft.CodeAnalysis.CSharp.CSharpParseOptions");
        var languageVersion = roslyn.GetType("Microsoft.CodeAnalysis.CSharp.LanguageVersion");
        var documentationMode = roslyn.GetType("Microsoft.CodeAnalysis.DocumentationMode");
        var sourceCodeKind = roslyn.GetType("Microsoft.CodeAnalysis.SourceCodeKind");
        foreach (var ctor in parseOptionsType.GetConstructors())
        {
            var ps = ctor.GetParameters();
            if (ps.Length == 4 && ps[3].ParameterType.IsAssignableFrom(typeof(string[])))
            {
                var symbols = defines.Length == 0 ? new string[0] : defines.Split(';');
                return ctor.Invoke(new object[] { Enum.ToObject(languageVersion, 0), Enum.ToObject(documentationMode, 1), Enum.ToObject(sourceCodeKind, 0), symbols });
            }
        }
        return null;
    }

    static object Parse(string path, string text, object parseOptions)
    {
        var treeClass = roslyn.GetType("Microsoft.CodeAnalysis.CSharp.CSharpSyntaxTree");
        foreach (var m in treeClass.GetMethods(BindingFlags.Public | BindingFlags.Static))
        {
            if (m.Name != "ParseText") continue;
            var ps = m.GetParameters();
            if (ps.Length == 5 && ps[0].ParameterType == typeof(string) && ps[2].ParameterType == typeof(string))
                return Invoke(m, null, Defaults(m, text, parseOptions, path));
        }
        throw new InvalidOperationException("no ParseText(string, options, path, ...)");
    }

    static Array References(bool everything)
    {
        var referenceType = roslyn.GetType("Microsoft.CodeAnalysis.MetadataReference");
        var fromFile = Find(referenceType, "CreateFromFile", 3, typeof(string));
        var runtime = Path.GetDirectoryName(typeof(object).Assembly.Location);
        var refs = new List<object>();
        if (everything)
        {
            foreach (var path in Directory.GetFiles(runtime, "*.dll"))
            {
                var name = Path.GetFileName(path);
                if (name.StartsWith("Microsoft.VisualBasic") || name.StartsWith("mscorlib") || name == "netstandard.dll") continue;
                if (name.StartsWith("System.") || name.StartsWith("Microsoft.") || name == "WindowsBase.dll")
                    refs.Add(Invoke(fromFile, null, Defaults(fromFile, path)));
            }
        }
        else
        {
            foreach (var name in new[] { "System.Private.CoreLib.dll", "System.Runtime.dll", "System.Console.dll", "System.Linq.dll", "System.Collections.dll" })
                refs.Add(Invoke(fromFile, null, Defaults(fromFile, Path.Combine(runtime, name))));
        }
        var array = Array.CreateInstance(referenceType, refs.Count);
        for (int i = 0; i < refs.Count; i++) array.SetValue(refs[i], i);
        return array;
    }

    /// `options` with the given diagnostic ids suppressed, the way a
    /// `<NoWarn>` does: Roslyn's own build turns RSEXPERIMENTAL006 off.
    static object Suppressing(object options, string ids)
    {
        if (string.IsNullOrEmpty(ids)) return options;
        var report = roslyn.GetType("Microsoft.CodeAnalysis.ReportDiagnostic");
        var pairType = typeof(KeyValuePair<string, int>).GetGenericTypeDefinition().MakeGenericType(typeof(string), report);
        var split = ids.Split(';');
        var pairs = Array.CreateInstance(pairType, split.Length);
        for (int i = 0; i < split.Length; i++)
            pairs.SetValue(Activator.CreateInstance(pairType, split[i], Enum.ToObject(report, 5)), i);
        foreach (var m in options.GetType().GetMethods())
        {
            if (m.Name != "WithSpecificDiagnosticOptions") continue;
            var ps = m.GetParameters();
            if (ps.Length == 1 && ps[0].ParameterType.IsAssignableFrom(pairs.GetType()))
                return m.Invoke(options, new object[] { pairs });
        }
        throw new InvalidOperationException("no WithSpecificDiagnosticOptions taking the pairs");
    }

    static object CompilationOptions(bool library)
    {
        var optionsType = roslyn.GetType("Microsoft.CodeAnalysis.CSharp.CSharpCompilationOptions");
        var outputKind = roslyn.GetType("Microsoft.CodeAnalysis.OutputKind");
        foreach (var ctor in optionsType.GetConstructors())
        {
            var ps = ctor.GetParameters();
            if (ps[0].ParameterType == outputKind && ps.Length > 5)
            {
                var arguments = new object[ps.Length];
                arguments[0] = Enum.ToObject(outputKind, 2);
                for (int i = 1; i < ps.Length; i++)
                {
                    arguments[i] = ps[i].HasDefaultValue ? ps[i].DefaultValue : (ps[i].ParameterType.IsValueType ? Activator.CreateInstance(ps[i].ParameterType) : null);
                    if (library && ps[i].Name == "allowUnsafe") arguments[i] = true;
                    // The same sources through the same compiler give the same bytes, which
                    // is how one generation is checked against the next.
                    if (ps[i].Name == "deterministic") arguments[i] = true;
                    if (library && ps[i].Name == "nullableContextOptions") arguments[i] = Enum.ToObject(ps[i].ParameterType, 3);
                }
                return ctor.Invoke(arguments);
            }
        }
        return null;
    }

    static object Create(string name, Array trees, Array references, object options)
    {
        var compilationType = roslyn.GetType("Microsoft.CodeAnalysis.CSharp.CSharpCompilation");
        var create = Find(compilationType, "Create", 4, typeof(string));
        return Invoke(create, null, new object[] { name, trees, references, options });
    }

    /// The manifest resources of `source`, described for Emit under the same names.
    static Array ResourcesFrom(Assembly source)
    {
        var descriptionType = roslyn.GetType("Microsoft.CodeAnalysis.ResourceDescription");
        ConstructorInfo ctor = null;
        foreach (var candidate in descriptionType.GetConstructors())
        {
            var ps = candidate.GetParameters();
            if (ps.Length == 3 && ps[0].ParameterType == typeof(string) && ps[1].ParameterType == typeof(Func<Stream>)) ctor = candidate;
        }
        var names = source.GetManifestResourceNames();
        var array = Array.CreateInstance(descriptionType, names.Length);
        for (int i = 0; i < names.Length; i++)
        {
            var name = names[i];
            var bytes = new MemoryStream();
            source.GetManifestResourceStream(name).CopyTo(bytes);
            var data = bytes.ToArray();
            Func<Stream> provider = () => new MemoryStream(data);
            array.SetValue(ctor.Invoke(new object[] { name, provider, true }), i);
        }
        return array;
    }

    static (bool success, byte[] image, object result) Emit(object compilation, Array resources)
    {
        var stream = new MemoryStream();
        MethodInfo emit = null;
        foreach (var m in compilation.GetType().GetMethods())
        {
            if (m.Name != "Emit") continue;
            var ps = m.GetParameters();
            if (ps.Length >= 6 && ps[0].ParameterType == typeof(Stream) && ps[1].ParameterType == typeof(Stream)
                && (resources == null || ps[4].ParameterType.IsAssignableFrom(resources.GetType()))) { emit = m; break; }
        }
        var arguments = Defaults(emit, stream);
        if (resources != null) arguments[4] = resources;
        var result = Invoke(emit, compilation, arguments);
        var success = (bool)result.GetType().GetProperty("Success").GetValue(result);
        return (success, stream.ToArray(), result);
    }

    static void PrintErrors(object result, int limit)
    {
        int errors = 0;
        foreach (var d in (System.Collections.IEnumerable)result.GetType().GetProperty("Diagnostics").GetValue(result))
        {
            var severity = d.GetType().GetProperty("Severity").GetValue(d).ToString();
            if (severity != "Error") continue;
            errors++;
            if (errors <= limit) Console.WriteLine("  " + Describe(d));
        }
        Console.WriteLine("emit errors: " + errors);
    }

    static void Main()
    {
        var args = Environment.GetCommandLineArgs();
        string input = args.Length > 1 ? args[1] : null;
        string roslynPath = Option(args, "--roslyn", "Roslyn.dll");
        string output = Option(args, "--out", null);
        string resourcesFrom = Option(args, "--resources-from", null);
        nowarn = Option(args, "--nowarn", "");
        roslyn = Assembly.LoadFrom(Path.GetFullPath(roslynPath));
        try
        {
            if (input == null || input.EndsWith(".cs"))
                RunCase(input, output);
            else
                CompileList(input, args.Length > 2 && !args[2].StartsWith("--") ? args[2] : "", Array.IndexOf(args, "--emit") >= 0, output, resourcesFrom);
        }
        catch (Exception e)
        {
            Report(e);
        }
    }

    static void RunCase(string path, string output)
    {
        var source = path == null
            ? "public static class C { public static int M(int x) => x + 1; public static string Greet(string who) => $\"hi {who}\"; }"
            : File.ReadAllText(path);
        var tree = Parse(path ?? "Program.cs", source, ParseOptions(""));
        var trees = Array.CreateInstance(roslyn.GetType("Microsoft.CodeAnalysis.SyntaxTree"), 1);
        trees.SetValue(tree, 0);
        var references = References(false);
        Console.WriteLine("references: " + references.Length);
        var options = Suppressing(CompilationOptions(false), nowarn);
        Console.WriteLine("options: " + (options != null));
        var compilation = Create("generated", trees, references, options);
        Console.WriteLine("compilation: " + compilation.GetType().Name);
        var getDiagnostics = Find(compilation.GetType(), "GetDiagnostics", 1, typeof(CancellationToken));
        int count = 0;
        foreach (var d in (System.Collections.IEnumerable)Invoke(getDiagnostics, compilation, new object[] { default(CancellationToken) }))
        {
            count++;
            if (count <= 10) Console.WriteLine("  " + Describe(d));
        }
        Console.WriteLine("diagnostics: " + count);
        var (success, image, result) = Emit(compilation, null);
        Console.WriteLine("emit success: " + success + " bytes: " + image.Length);
        if (!success) { PrintErrors(result, 30); return; }
        if (output != null) File.WriteAllBytes(output, image);
        var produced = Assembly.Load(image);
        var c = produced.GetType("C");
        var m = c.GetMethod("M");
        if (m != null) Console.WriteLine("M(41) = " + m.Invoke(null, new object[] { 41 }));
        var greet = c.GetMethod("Greet");
        if (greet != null) Console.WriteLine("Greet = " + greet.Invoke(null, new object[] { "roslyn" }));
        var run = c.GetMethod("Run");
        if (run != null) Console.WriteLine("Run = " + run.Invoke(null, null));
    }

    static void CompileList(string listFile, string defines, bool emit, string output, string resourcesFrom)
    {
        var watch = Stopwatch.StartNew();
        var parseOptions = ParseOptions(defines);
        Console.WriteLine("parse options: " + (parseOptions != null) + " defines: " + defines);
        var files = File.ReadAllLines(listFile);
        var trees = Array.CreateInstance(roslyn.GetType("Microsoft.CodeAnalysis.SyntaxTree"), files.Length);
        int parseDiagnostics = 0;
        for (int i = 0; i < files.Length; i++)
        {
            if (files[i].Length == 0) continue;
            object tree;
            try { tree = Parse(files[i], File.ReadAllText(files[i]), parseOptions); }
            catch (Exception e) { Console.WriteLine("parse failed: " + files[i]); Report(e); return; }
            trees.SetValue(tree, i);
            var getDiagnostics = Find(tree.GetType(), "GetDiagnostics", 1, typeof(CancellationToken));
            foreach (var d in (System.Collections.IEnumerable)Invoke(getDiagnostics, tree, new object[] { default(CancellationToken) }))
            {
                parseDiagnostics++;
                if (parseDiagnostics <= 10) Console.WriteLine("  parse: " + Describe(d));
            }
        }
        Console.WriteLine("parsed " + files.Length + " files in " + watch.ElapsedMilliseconds + " ms, parse diagnostics: " + parseDiagnostics);
        watch.Restart();
        var references = References(true);
        Console.WriteLine("references: " + references.Length + " in " + watch.ElapsedMilliseconds + " ms");
        watch.Restart();
        var options = Suppressing(CompilationOptions(true), nowarn);
        var compilation = Create("corpus", trees, references, options);
        var getAll = Find(compilation.GetType(), "GetDiagnostics", 1, typeof(CancellationToken));
        var diagnostics = Invoke(getAll, compilation, new object[] { default(CancellationToken) });
        int count = 0, shown = 0;
        var bySeverity = new Dictionary<string, int>();
        var byId = new Dictionary<string, int>();
        foreach (var d in (System.Collections.IEnumerable)diagnostics)
        {
            count++;
            var severity = d.GetType().GetProperty("Severity").GetValue(d).ToString();
            bySeverity[severity] = bySeverity.TryGetValue(severity, out var n) ? n + 1 : 1;
            var id = d.GetType().GetProperty("Id").GetValue(d).ToString();
            byId[id] = byId.TryGetValue(id, out var k) ? k + 1 : 1;
            if (severity == "Error" && shown++ < 40) Console.WriteLine("  " + Describe(d));
        }
        Console.WriteLine("diagnostics: " + count + " in " + watch.ElapsedMilliseconds + " ms");
        foreach (var pair in bySeverity) Console.WriteLine("  " + pair.Key + ": " + pair.Value);
        var ids = new List<KeyValuePair<string, int>>(byId);
        ids.Sort((a, b) => b.Value.CompareTo(a.Value));
        for (int i = 0; i < ids.Count && i < 15; i++) Console.WriteLine("  " + ids[i].Key + " x" + ids[i].Value);
        watch.Restart();
        if (!emit) return;
        var resources = ResourcesFrom(resourcesFrom == null ? roslyn : Assembly.LoadFrom(Path.GetFullPath(resourcesFrom)));
        var (success, image, result) = Emit(compilation, resources);
        Console.WriteLine("emit success: " + success + " bytes: " + image.Length + " resources: " + resources.Length + " in " + watch.ElapsedMilliseconds + " ms");
        if (success) File.WriteAllBytes(output ?? "Corpus.dll", image);
        else PrintErrors(result, 30);
    }
}
