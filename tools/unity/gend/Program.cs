// Keeps the source generators of a Unity assembly running: the compilation
// they see stays in memory, and an edit replaces one tree and runs the
// incremental generators again, which redo only what the edit reaches. What
// they produce is written where csc's -generatedfilesout puts it — the
// generator's assembly, then its type, then the hint name — and only the
// files whose text changed are touched.
//
// usage: gend <Assembly.rsp> <project root> <out directory> [sources list]
// stdin: one line per change: a source path (edited or added), "- path"
// (removed); "run" runs the generators for all of them and answers one line,
// with a tab and each file written after it (a `-` before one deleted);
// "quit". A generated file is written wherever its text on disk differs,
// whoever wrote it.
using System.Collections.Concurrent;
using System.Collections.Immutable;
using System.Diagnostics;
using System.Reflection;
using System.Runtime.Loader;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.Text;

var (rsp, root, output) = (args[0], args[1], args[2]);
Directory.SetCurrentDirectory(root);
var watch = Stopwatch.StartNew();

var references = new List<string>();
var defines = new List<string>();
var sources = new List<string>();
var analyzers = new List<string>();
var additional = new List<string>();
foreach (var raw in File.ReadAllLines(rsp))
{
    var entry = raw.Trim();
    string Value(string prefix) => entry.Substring(prefix.Length).Trim('"');
    if (entry.StartsWith("-r:")) references.Add(Value("-r:"));
    else if (entry.StartsWith("-define:")) defines.Add(Value("-define:"));
    else if (entry.StartsWith("-analyzer:")) analyzers.Add(Value("-analyzer:"));
    else if (entry.StartsWith("/additionalfile:")) additional.Add(Value("/additionalfile:"));
    else if (!entry.StartsWith("-") && !entry.StartsWith("/") && (entry.EndsWith(".cs\"") || entry.EndsWith(".cs")))
        sources.Add(entry.Trim('"'));
}

// A list of the project's sources given after the output directory — the
// daemon's, kept up to date as files come and go — stands for the ones in
// the response file.
if (args.Length > 3 && File.Exists(args[3]))
    sources = File.ReadAllLines(args[3]).Select(line => line.Trim())
        .Where(line => line.EndsWith(".cs") && !Path.IsPathRooted(line)).ToList();
// A file listed that is gone — deleted since the list was made — is not
// one of the assembly's any more.
sources = sources.Where(File.Exists).ToList();
var parseOptions = new CSharpParseOptions(LanguageVersion.CSharp9, preprocessorSymbols: defines);
SyntaxTree Parse(string path) =>
    CSharpSyntaxTree.ParseText(SourceText.From(new MemoryStream(File.ReadAllBytes(path)), Encoding.UTF8), parseOptions, path);

var trees = new ConcurrentDictionary<string, SyntaxTree>();
Parallel.ForEach(sources, path => trees[path] = Parse(path));
var metadata = references.AsParallel().Select(path => (MetadataReference)MetadataReference.CreateFromFile(path)).ToList();
var compilation = CSharpCompilation.Create(
    "Assembly-CSharp",
    sources.Select(path => trees[path]),
    metadata,
    new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true));
Console.WriteLine($"parsed {sources.Count} files in {watch.ElapsedMilliseconds} ms");

var loader = new Loader();
var generators = analyzers
    .Select(path => new AnalyzerFileReference(Path.GetFullPath(path), loader))
    .SelectMany(reference => reference.GetGenerators(LanguageNames.CSharp))
    .ToImmutableArray();
var texts = additional
    .Select(path => (AdditionalText)new FileText(Path.GetFullPath(path)))
    .ToImmutableArray();
GeneratorDriver driver = CSharpGeneratorDriver.Create(generators, texts, parseOptions);

var produced = new Dictionary<string, string>();
var failures = new List<string>();
(int changed, int added, int removed, List<string> paths) Run()
{
    driver = driver.RunGenerators(compilation);
    var result = driver.GetRunResult();
    var now = new Dictionary<string, string>();
    failures.Clear();
    foreach (var run in result.Results)
    {
        var type = run.Generator.GetGeneratorType();
        var folder = Path.Combine(output, type.Assembly.GetName().Name, type.FullName);
        // A generator that threw said nothing: what it wrote last stays.
        if (run.Exception != null)
        {
            failures.Add($"{type.Name}: {run.Exception.GetType().Name}: {run.Exception.Message.Replace('\n', ' ')}");
            foreach (var kept in produced.Where(entry => entry.Key.StartsWith(folder + Path.DirectorySeparatorChar)))
                now[kept.Key] = kept.Value;
            continue;
        }
        foreach (var source in run.GeneratedSources)
            now[Path.Combine(folder, source.HintName)] = source.SourceText.ToString();
    }
    // A generator names some files with a token of its run (`Name.component_
    // <guid>.g.cs`): a file it writes again for the same type keeps the name
    // it had, or every run would rename thousands.
    var gone = produced.Keys.Where(path => !now.ContainsKey(path))
        .GroupBy(path => (Path.GetDirectoryName(path), Stem(path)))
        .Where(group => group.Count() == 1)
        .ToDictionary(group => group.Key, group => group.Single());
    foreach (var path in now.Keys.Where(path => !produced.ContainsKey(path)).ToList())
    {
        var key = (Path.GetDirectoryName(path), Stem(path));
        if (!gone.TryGetValue(key, out var kept)) continue;
        now[kept] = now[path];
        now.Remove(path);
        gone.Remove(key);
    }
    var paths = new List<string>();
    int changed = 0, added = 0, removed = 0;
    foreach (var (path, text) in now)
    {
        var onDisk = File.Exists(path) ? File.ReadAllText(path) : null;
        if (onDisk != null && onDisk.TrimStart('\uFEFF') == text.TrimStart('\uFEFF')) continue;
        if (produced.ContainsKey(path)) changed++; else added++;
        Directory.CreateDirectory(Path.GetDirectoryName(path));
        File.WriteAllText(path, text, new UTF8Encoding(false));
        paths.Add(path);
    }
    foreach (var path in produced.Keys.Where(path => !now.ContainsKey(path)).ToList())
    {
        File.Delete(path);
        removed++;
        paths.Add("- " + path);
    }
    produced = now;
    return (changed, added, removed, paths);
}

var first = Stopwatch.StartNew();
// What an earlier run left is taken as this one's: a file written again for
// the same type keeps its name, and one whose text is the same is not
// written at all.
foreach (var file in Directory.Exists(output) ? Directory.EnumerateFiles(output, "*.cs", SearchOption.AllDirectories) : Enumerable.Empty<string>())
    produced[file] = File.ReadAllText(file);
var initial = Run();
// What another run left in the directory — csc's, or an earlier daemon's,
// under hint names of their own — is not this run's, and goes.
foreach (var stale in Directory.EnumerateFiles(output, "*.cs", SearchOption.AllDirectories)
    .Where(path => !produced.ContainsKey(path)).ToList())
    File.Delete(stale);
Console.WriteLine($"ready {first.ElapsedMilliseconds} ms, {produced.Count} files, {initial.paths.Count} written"
    + (failures.Count > 0 ? ", threw: " + string.Join(" | ", failures).Replace('\t', ' ') : "")
    + string.Concat(initial.paths.Select(path => "\t" + (path.StartsWith("- ") ? "-" + path.Substring(2) : path))));

// Edits are gathered until "run": the generators run once for all of them.
string line;
var pending = 0;
while ((line = Console.ReadLine()) != null)
{
    line = line.Trim();
    if (line.Length == 0) continue;
    if (line == "quit") break;
    try
    {
        if (line == "run")
        {
            var round = Stopwatch.StartNew();
            var (changed, added, removed, paths) = Run();
            // Then each file written, and each deleted with a `-` before it.
            Console.WriteLine($"generated {round.ElapsedMilliseconds} ms, {pending} edits, {changed} changed, {added} added, {removed} removed"
                + (failures.Count > 0 ? ", threw: " + string.Join(" | ", failures).Replace('\t', ' ') : "")
                + string.Concat(paths.Select(path => "\t" + (path.StartsWith("- ") ? "-" + path.Substring(2) : path))));
            pending = 0;
            continue;
        }
        pending++;
        if (line.StartsWith("- "))
        {
            var path = line.Substring(2);
            if (trees.TryRemove(path, out var tree)) compilation = compilation.RemoveSyntaxTrees(tree);
        }
        else
        {
            var path = line.StartsWith("+ ") ? line.Substring(2) : line;
            var tree = Parse(path);
            if (trees.TryGetValue(path, out var old)) compilation = compilation.ReplaceSyntaxTree(old, tree);
            else compilation = compilation.AddSyntaxTrees(tree);
            trees[path] = tree;
        }
    }
    catch (Exception error)
    {
        Console.WriteLine($"failed {line}: {error.Message}");
    }
}

static string Stem(string file)
{
    var name = Path.GetFileName(file);
    var underscore = name.LastIndexOf('_');
    return underscore > 0 ? name.Substring(0, underscore + 1) : name;
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
