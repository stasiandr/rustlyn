// Runs a Unity assembly's source generators on one edited file alone, against
// the assembly as built, and puts what they make for it over the files they
// made for it before. A generator here writes one file per type it reads, so
// a compilation of the edited file is all it needs to say again what it says
// about that file's types — in a fraction of the time the whole assembly
// takes.
//
// Some generators read the whole assembly besides the type they write for:
// the middlewares every system's update goes through are found by their
// attributes. The files that match <context> join every run.
//
// usage: minigen <Assembly.rsp> <project root> <generated directory> <built assembly> <context regex> [sources list]
// The sources list, one path a line, stands for the rsp's where the files
// have changed since it was written.
// stdin: one edited source path per line, "check <n>" to compare n sources'
// output with what is on disk without writing, or "quit".
// stdout: per line, "gen <ms>" then a tab and each generated file for the
// edited one, written again where it changed; or "failed <why>".
using System.Collections.Immutable;
using System.Diagnostics;
using System.Reflection;
using System.Runtime.Loader;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.Text;

var (rsp, root, output, built) = (args[0], args[1], args[2], args[3]);
var context = new System.Text.RegularExpressions.Regex(args.Length > 4 ? args[4] : "(?!)");
Directory.SetCurrentDirectory(root);
var watch = Stopwatch.StartNew();

var references = new List<string>();
var defines = new List<string>();
var analyzers = new List<string>();
var additional = new List<string>();
var sources = new List<string>();
foreach (var raw in File.ReadAllLines(rsp))
{
    var entry = raw.Trim();
    string Value(string prefix) => entry.Substring(prefix.Length).Trim('"');
    if (entry.StartsWith("-r:")) references.Add(Value("-r:"));
    else if (entry.StartsWith("-define:")) defines.Add(Value("-define:"));
    else if (entry.StartsWith("-analyzer:")) analyzers.Add(Value("-analyzer:"));
    else if (entry.StartsWith("/additionalfile:")) additional.Add(Value("/additionalfile:"));
    else if (!entry.StartsWith("-") && !entry.StartsWith("/") && entry.Trim('"').EndsWith(".cs"))
        sources.Add(entry.Trim('"'));
}
references.Add(built);
if (args.Length > 5)
    sources = File.ReadAllLines(args[5]).Select(line => line.Trim()).Where(line => line.EndsWith(".cs")).ToList();
// What the generators wrote is theirs to write again, not something they read.
var generatedRoot = Path.GetFullPath(output);
sources = sources.Where(path => File.Exists(path) && !Path.GetFullPath(path).StartsWith(generatedRoot)).ToList();

var parseOptions = new CSharpParseOptions(LanguageVersion.CSharp9, preprocessorSymbols: defines);
var metadata = references.AsParallel().Select(path => (MetadataReference)MetadataReference.CreateFromFile(path)).ToList();
var compilationOptions = new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true);
SyntaxTree Parse(string path) =>
    CSharpSyntaxTree.ParseText(SourceText.From(new MemoryStream(File.ReadAllBytes(path)), Encoding.UTF8), parseOptions, path);
// What the generators wrote is not a source of the types it is about: the
// output folder by where it is, and `/gen/` as the daemon has named it.
var outputFolder = Path.GetFullPath(output).TrimEnd('/') + "/";
bool Written(string path) => path.Contains("/gen/") || Path.GetFullPath(path, root).StartsWith(outputFolder);
var contextFiles = sources.AsParallel().Where(path => context.IsMatch(File.ReadAllText(path))).ToList();
var contextTrees = contextFiles.Select(Parse).ToList();

// Which files declare a type of each name: a generator that writes for a
// feature reads the systems it lists, so the files of the types an edited
// file names come with it.
var declaring = new Dictionary<string, List<string>>();
foreach (var (path, names) in sources.Where(path => !Written(path)).AsParallel()
    .Select(path => (path, names: TypeNames(Parse(path).GetRoot()).ToList())).ToList())
    foreach (var name in names)
    {
        if (!declaring.TryGetValue(name, out var list)) declaring[name] = list = new List<string>();
        list.Add(path);
    }
static IEnumerable<string> TypeNames(SyntaxNode root) =>
    root.DescendantNodes(node => node is not Microsoft.CodeAnalysis.CSharp.Syntax.BaseMethodDeclarationSyntax)
        .OfType<Microsoft.CodeAnalysis.CSharp.Syntax.BaseTypeDeclarationSyntax>()
        .Select(type => type.Identifier.ValueText)
        .Distinct();

var loader = new Loader();
// Generators that gather the whole assembly into one file: run on one file,
// they would say the assembly is that file.
var gathering = new HashSet<string>
{
    "MonoScriptInfoGenerator",
    "ConfigPrewarmGenerator",
    "ConfigPrewarmJsonObjectsGenerator",
    "FeatureRunnerSourceGenerator",
};
var generators = analyzers
    .Select(path => new AnalyzerFileReference(Path.GetFullPath(path), loader))
    .SelectMany(reference => reference.GetGenerators(LanguageNames.CSharp))
    .Where(generator => !gathering.Contains(generator.GetGeneratorType().Name))
    .ToImmutableArray();
var texts = additional
    .Select(path => (AdditionalText)new FileText(Path.GetFullPath(path)))
    .ToImmutableArray();

// A hint name ends in a token of its own run (`Name.system_<guid>.g.cs`): the
// file a generator made before for the same type is found by what precedes
// it, and by the namespace it declares where two types share a name.
static string Stem(string file)
{
    var name = Path.GetFileName(file);
    var underscore = name.LastIndexOf('_');
    return underscore > 0 ? name.Substring(0, underscore + 1) : name;
}
var existing = new Dictionary<(string folder, string stem), List<string>>();
foreach (var file in Directory.EnumerateFiles(output, "*.cs", SearchOption.AllDirectories))
{
    var key = (Path.GetDirectoryName(file), Stem(file));
    if (!existing.TryGetValue(key, out var list)) existing[key] = list = new List<string>();
    list.Add(file);
}
static string NamespaceOf(string text)
{
    foreach (var line in text.Split('\n'))
    {
        var trimmed = line.Trim();
        if (trimmed.StartsWith("namespace ")) return trimmed.TrimEnd('{', ' ', ';');
    }
    return "";
}

// One run, to load and warm every generator before the first edit.
CSharpGeneratorDriver.Create(generators, texts, parseOptions)
    .RunGenerators(CSharpCompilation.Create("Assembly-CSharp", Array.Empty<SyntaxTree>(), metadata, compilationOptions));
Console.WriteLine($"ready {watch.ElapsedMilliseconds} ms, {generators.Length} generators, {existing.Count} kinds of file, {contextFiles.Count} context files");

// What the generators make for `path`: each file, where it goes, and whether
// that differs from what is there.
List<(string target, string text, bool changed)> Generate(string path)
{
    var edited = Parse(path);
    var own = TypeNames(edited.GetRoot()).ToHashSet();
    foreach (var name in own)
    {
        if (!declaring.TryGetValue(name, out var list)) declaring[name] = list = new List<string>();
        if (!list.Contains(path)) list.Add(path);
    }
    var named = edited.GetRoot().DescendantTokens()
        .Where(token => token.IsKind(SyntaxKind.IdentifierToken))
        .Select(token => token.ValueText)
        .Where(name => !own.Contains(name))
        .ToHashSet();
    var neighbours = named
        .SelectMany(name => declaring.TryGetValue(name, out var files) ? files : Enumerable.Empty<string>())
        .Where(file => file != path && !contextFiles.Contains(file))
        .Distinct()
        .Select(Parse);
    var trees = contextTrees.Where(tree => tree.FilePath != path).Concat(neighbours).Append(edited);
    var compilation = CSharpCompilation.Create("Assembly-CSharp", trees, metadata, compilationOptions);
    var driver = CSharpGeneratorDriver.Create(generators, texts, parseOptions).RunGenerators(compilation);
    var made = new List<(string, string, bool)>();
    foreach (var run in driver.GetRunResult().Results)
    {
        var type = run.Generator.GetGeneratorType();
        var folder = Path.Combine(output, type.Assembly.GetName().Name, type.FullName);
        foreach (var source in run.GeneratedSources)
        {
            // What the other files bring is theirs, and as they were.
            var hint = Path.GetFileName(source.HintName);
            if (!own.Any(name => hint.StartsWith(name + ".") || hint.StartsWith(name + "_")))
                continue;
            var text = source.SourceText.ToString();
            var key = (folder, Stem(source.HintName));
            string target = null;
            if (existing.TryGetValue(key, out var candidates))
            {
                var space = NamespaceOf(text);
                target = candidates.Count == 1
                    ? candidates[0]
                    : candidates.FirstOrDefault(candidate => NamespaceOf(File.ReadAllText(candidate)) == space);
            }
            if (target == null)
            {
                made.Add((Path.Combine(folder, source.HintName), text, true));
                continue;
            }
            made.Add((target, text, File.ReadAllText(target).TrimStart('\uFEFF') != text.TrimStart('\uFEFF')));
        }
    }
    return made;
}

string line;
while ((line = Console.ReadLine()) != null)
{
    line = line.Trim();
    if (line.Length == 0) continue;
    if (line == "quit") break;
    var round = Stopwatch.StartNew();
    try
    {
        if (line.StartsWith("check "))
        {
            var count = int.Parse(line.Substring(6));
            var random = new Random(1);
            var picked = sources.Where(path => !Written(path)).OrderBy(_ => random.Next()).Take(count).ToList();
            int differ = 0, fresh = 0;
            foreach (var path in picked)
                foreach (var (target, text, changed) in Generate(path))
                {
                    if (!changed) continue;
                    if (File.Exists(target)) { differ++; var side = Path.Combine(Path.GetTempPath(), "minigen-" + differ + ".cs"); File.WriteAllText(side, text); Console.Error.WriteLine($"differs {path} -> {target} {side}"); }
                    else { fresh++; Console.Error.WriteLine($"new {path} -> {target}"); }
                }
            Console.WriteLine($"checked {picked.Count} in {round.ElapsedMilliseconds} ms: {differ} differ, {fresh} new");
            continue;
        }
        // `rescan` and the files saved, a tab between each two: what another
        // generator run wrote is read from the directory again, and which
        // files declare which types from the saved ones.
        if (line.StartsWith("rescan"))
        {
            existing.Clear();
            foreach (var file in Directory.EnumerateFiles(output, "*.cs", SearchOption.AllDirectories))
            {
                var key = (Path.GetDirectoryName(file), Stem(file));
                if (!existing.TryGetValue(key, out var list)) existing[key] = list = new List<string>();
                list.Add(file);
            }
            foreach (var saved in line.Split('\t').Skip(1))
            {
                foreach (var entry in declaring.Values) entry.Remove(saved);
                if (!File.Exists(saved)) continue;
                foreach (var name in TypeNames(Parse(saved).GetRoot()))
                {
                    if (!declaring.TryGetValue(name, out var list)) declaring[name] = list = new List<string>();
                    list.Add(saved);
                }
            }
            Console.WriteLine($"gen {round.ElapsedMilliseconds}");
            continue;
        }
        // A file that is gone takes what the generators wrote for its types
        // along, where no other file declares them: each such file is
        // named with a `-` before it, and deleted.
        if (line.StartsWith("delete "))
        {
            var gone = line.Substring(7);
            var removed = new List<string>();
            foreach (var name in declaring.Where(entry => entry.Value.Contains(gone)).Select(entry => entry.Key).ToList())
            {
                declaring[name].Remove(gone);
                if (declaring[name].Count > 0) continue;
                declaring.Remove(name);
                foreach (var key in existing.Keys.Where(key => key.stem.StartsWith(name + ".") || key.stem.StartsWith(name + "_")).ToList())
                {
                    // Two types of one name in two namespaces: which was this
                    // file's is not known any more, and both stay.
                    if (existing[key].Count != 1) continue;
                    File.Delete(existing[key][0]);
                    removed.Add("-" + existing[key][0]);
                    existing.Remove(key);
                }
            }
            Console.WriteLine($"gen {round.ElapsedMilliseconds}" + string.Concat(removed.Select(path => "\t" + path)));
            continue;
        }
        // Every file the generators write for the edited one is named, changed
        // or not: whoever asked may not have the one on disk yet.
        var written = new List<string>();
        foreach (var (target, text, changed) in Generate(line))
        {
            if (!changed)
            {
                written.Add(target);
                continue;
            }
            Directory.CreateDirectory(Path.GetDirectoryName(target));
            File.WriteAllText(target, text, new UTF8Encoding(false));
            var key = (Path.GetDirectoryName(target), Stem(target));
            if (!existing.TryGetValue(key, out var list)) existing[key] = list = new List<string>();
            if (!list.Contains(target)) list.Add(target);
            written.Add(target);
        }
        // What the generators wrote before for a type of this file alone
        // and write no more — its last [Injectable] field gone, say — goes,
        // named with a `-` before it.
        var mine = TypeNames(Parse(line).GetRoot())
            .Where(name => declaring.TryGetValue(name, out var files) && files.Count == 1 && files[0] == line)
            .ToList();
        foreach (var key in existing.Keys.ToList())
        {
            if (!mine.Any(name => key.stem.StartsWith(name + ".") || key.stem.StartsWith(name + "_"))) continue;
            if (existing[key].Count != 1 || written.Contains(existing[key][0])) continue;
            File.Delete(existing[key][0]);
            written.Add("-" + existing[key][0]);
            existing.Remove(key);
        }
        Console.WriteLine($"gen {round.ElapsedMilliseconds}" + string.Concat(written.Select(path => "\t" + path)));
    }
    catch (Exception error)
    {
        Console.WriteLine($"failed {line}: {error.Message.Replace('\n', ' ')}");
    }
}

sealed class Loader : IAnalyzerAssemblyLoader
{
    public void AddDependencyLocation(string fullPath) { }
    public Assembly LoadFromPath(string fullPath) => AssemblyLoadContext.Default.LoadFromAssemblyPath(fullPath);
}

sealed class FileText : AdditionalText
{
    public FileText(string path) { Path = path; }
    public override string Path { get; }
    public override SourceText GetText(CancellationToken cancellationToken = default) =>
        SourceText.From(File.ReadAllText(Path), Encoding.UTF8);
}
