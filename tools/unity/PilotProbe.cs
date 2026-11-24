// Pilot's probe for building Assembly-CSharp outside Unity.
//
// It lives only in the experimental copy of the project. Unity is driven
// through files in Temp/PilotProbe: a line written to cmd.txt is one command,
// and each answer is appended to log.txt.
//
//   reload[p] <path to Assembly-CSharp.dll>  put that assembly in place of the one
//                                        Unity built, and reload the scripts
//                                        without compiling anything
//   verify                               load every type of Assembly-CSharp and
//                                        JIT every method, and check that every
//                                        MonoScript still finds its class
//   call <Type> <Method>                 call a static method of Assembly-CSharp
//                                        with no arguments and say what it gave
//   hotpatch <PilotPatch-n.dll>          apply a patch the daemon wrote: each
//                                        line of the .txt beside it names a
//                                        method and the static one replacing it
//   patch <dll> <Type> <Method>          send calls of Assembly-CSharp's method
//                                        to the same static method of that dll,
//                                        without reloading anything
//   perf [s]                             the editor's own trackers whose last
//                                        sample took at least that long
//   refresh                              let Unity import and compile what
//                                        changed, as a focused editor would
//   note <text>                          show what the watcher did with a save
//   hud                                  open Window > Pilot Hot Reload
//   quit                                 leave the editor
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Reflection;
using UnityEditor;
using UnityEngine;
using Debug = UnityEngine.Debug;

[InitializeOnLoad]
static class PilotProbe
{
    const string Directory = "Temp/PilotProbe";
    const string StartedKey = "PilotProbe.reloadStarted";
    const string BeforeKey = "PilotProbe.beforeReload";
    // While an editor patches this one (`hold on`), Unity's own compiles do
    // not reload it: the build that editor measures patches against stays,
    // and so do the patches. Held across reloads, given back with `hold
    // off` — or when the holder's heartbeat file is a minute old.
    const string HoldKey = "PilotProbe.hold";
    // The PilotRuntime `load` put in the editor, to put in again after the probe's own reload.
    const string LoadsKey = "PilotProbe.loads";
    // Whether this editor session has auto refresh turned off by the probe.
    const string NoAutoRefreshKey = "PilotProbe.noAutoRefresh";
    static readonly string Heartbeat = Path.Combine(Directory, "hold");
    // When Pilot was last seen alive, in Library: Unity wipes Temp when it
    // quits. A probe Pilot has not come for in an hour takes itself out of
    // the project, and the editor is as it was without Pilot.
    const string Seen = "Library/PilotProbe/seen";
    static readonly TimeSpan Unattended = TimeSpan.FromHours(1);
    static double seenChecked = -1000;
    static bool holding;
    // Unity's own compile, from start to finish: under a hold
    // EditorApplication.isCompiling stays true until the reload it waits for.
    static bool compilingNow;
    // A reload asked for while Unity compiled: its output would be copied
    // over the one put in place, so the reload waits for the compile.
    static (string path, bool partial)? deferredReload;
    // Unity compiled while held: its build waits to be loaded, and Play Mode
    // will not start until it is.
    static bool compiledWhileHeld;
    static double enteringPlay = -1;

    static void ReleaseForPlay()
    {
        enteringPlay = -1;
        Hold(false);
        Answer("hold released for Play Mode: Unity loads its own build");
    }
    static DateTime constructed;
    static readonly string Commands = Path.Combine(Directory, "cmd.txt");
    static readonly string Log = Path.Combine(Directory, "log.txt");
    static double polled;

    static PilotProbe()
    {
        constructed = DateTime.UtcNow;
        System.IO.Directory.CreateDirectory(Directory);
        AssemblyReloadEvents.beforeAssemblyReload += () =>
        {
            if (SessionState.GetString(StartedKey, "").Length > 0)
                SessionState.SetString(BeforeKey, DateTime.UtcNow.Ticks.ToString());
        };
        // Nothing but the probe decides when scripts reload: an edit on disk
        // must not start Unity's own compile. The editor counts these for the
        // whole session, across reloads: once a session, or one Allow would
        // never undo them.
        if (!SessionState.GetBool(NoAutoRefreshKey, false))
        {
            AssetDatabase.DisallowAutoRefresh();
            SessionState.SetBool(NoAutoRefreshKey, true);
        }
        var assembly = GameAssembly();
        var started = SessionState.GetString(StartedKey, "");
        if (started.Length > 0)
        {
            SessionState.EraseString(StartedKey);
            var begun = new DateTime(long.Parse(started), DateTimeKind.Utc);
            var loadedIn = (DateTime.UtcNow - begun).TotalMilliseconds;
            var before = SessionState.GetString(BeforeKey, "");
            SessionState.EraseString(BeforeKey);
            var reloadStarts = before.Length > 0
                ? (new DateTime(long.Parse(before), DateTimeKind.Utc) - begun).TotalMilliseconds
                : -1;
            // What was loaded into the editor before goes in again, and the
            // hold is back: in the background each command waits for an
            // update of the editor's, seconds apart.
            var loads = 0;
            foreach (var path in new[] { SessionState.GetString(LoadsKey, "") }.Where(path => path.Length > 0))
            {
                try { Assembly.Load(File.ReadAllBytes(path)); loads++; }
                // Not "failed": whoever waits for the reload would take it for
                // the reload's own failure. Without it `load` is asked again.
                catch (Exception error) { Answer($"runtime not loaded again: {error.Message}"); }
            }
            if (SessionState.GetBool(HoldKey, false)) Hold(true);
            // Said now: an editor in the background may not get to a
            // delayed call until it is in front again, and whoever waits
            // for the reload would wait as long.
            Answer($"reloaded loaded={loadedIn:F0}ms beforeReload={reloadStarts:F0}ms assembly={Describe(assembly)} loads={loads} holding={holding}");
            EditorApplication.delayCall += () =>
                Answer($"usable after {(DateTime.UtcNow - begun).TotalMilliseconds:F0}ms");
        }
        else
        {
            Answer($"started assembly={Describe(assembly)}");
        }
        if (SessionState.GetBool(HoldKey, false)) Hold(true);
        UnityEditor.Compilation.CompilationPipeline.compilationStarted += _ => compilingNow = true;
        UnityEditor.Compilation.CompilationPipeline.compilationFinished += _ =>
        {
            compilingNow = false;
            if (holding) compiledWhileHeld = true;
            if (deferredReload is { } waiting)
            {
                deferredReload = null;
                EditorApplication.delayCall += () => Reload(waiting.path, waiting.partial);
            }
        };
        EditorApplication.update += Poll;
        // Whoever patches the editor has to know when Play Mode starts and
        // stops: entering it may make Unity compile and reload on its own.
        EditorApplication.playModeStateChanged += change =>
        {
            Answer($"play state {change}");
            // Play Mode waits for the build Unity compiled to load, which the
            // hold keeps from loading: let it go rather than hang.
            if (change == PlayModeStateChange.ExitingEditMode && holding)
            {
                if (compiledWhileHeld || compilingNow) ReleaseForPlay();
                // Unity may also find script changes only now, and wait for
                // a reload the hold keeps from happening.
                else enteringPlay = EditorApplication.timeSinceStartup;
            }
            if (change == PlayModeStateChange.EnteredPlayMode) enteringPlay = -1;
        };
        // An assembly loaded from bytes is found by name only if asked for.
        AppDomain.CurrentDomain.AssemblyResolve += (sender, request) =>
            AppDomain.CurrentDomain.GetAssemblies()
                .FirstOrDefault(assembly => assembly.GetName().Name == new AssemblyName(request.Name).Name);
    }

    static void Hold(bool on)
    {
        if (on == holding) return;
        holding = on;
        SessionState.SetBool(HoldKey, on);
        if (on) EditorApplication.LockReloadAssemblies();
        else EditorApplication.UnlockReloadAssemblies();
    }

    static void Poll()
    {
        if (EditorApplication.timeSinceStartup - polled < 0.05) return;
        polled = EditorApplication.timeSinceStartup;
        if (holding && enteringPlay >= 0 && EditorApplication.timeSinceStartup - enteringPlay > 3)
            ReleaseForPlay();
        if (holding && (!File.Exists(Heartbeat) || (DateTime.UtcNow - File.GetLastWriteTimeUtc(Heartbeat)).TotalSeconds > 60))
        {
            Hold(false);
            Answer("hold released: no heartbeat");
        }
        if (EditorApplication.timeSinceStartup - seenChecked > 30)
        {
            seenChecked = EditorApplication.timeSinceStartup;
            CheckPilot();
        }
        if (!File.Exists(Commands)) return;
        var lines = File.ReadAllLines(Commands);
        File.Delete(Commands);
        MarkSeen();
        foreach (var line in lines.Where(line => line.Trim().Length > 0))
        {
            try { Run(line.Trim()); }
            catch (Exception error) { Answer($"failed {line}: {error}"); }
        }
    }

    static void MarkSeen()
    {
        System.IO.Directory.CreateDirectory(Path.GetDirectoryName(Seen));
        File.WriteAllText(Seen, DateTime.UtcNow.Ticks.ToString());
    }

    // Pilot alive — its heartbeat is fresh — or gone long enough that the
    // probe is only in the way: auto refresh off, a build Unity did not make.
    static void CheckPilot()
    {
        if (File.Exists(Heartbeat) && (DateTime.UtcNow - File.GetLastWriteTimeUtc(Heartbeat)).TotalSeconds < 60)
        {
            MarkSeen();
            return;
        }
        if (!File.Exists(Seen) || !long.TryParse(File.ReadAllText(Seen).Trim(), out var ticks))
        {
            // Never seen yet: counted from now.
            MarkSeen();
            return;
        }
        // A Pilot started with the editor gets to it first.
        if (EditorApplication.timeSinceStartup < 300) return;
        if (DateTime.UtcNow - new DateTime(ticks, DateTimeKind.Utc) < Unattended) return;
        Answer("removing the probe: no Pilot for an hour");
        if (holding) Hold(false);
        if (SessionState.GetBool(NoAutoRefreshKey, false))
        {
            AssetDatabase.AllowAutoRefresh();
            SessionState.EraseBool(NoAutoRefreshKey);
        }
        File.Delete(Seen);
        // The game's assembly in the editor is Pilot's build: without it, the
        // compile the removal makes puts Unity's own in its place.
        File.Delete("Library/ScriptAssemblies/Assembly-CSharp.dll");
        File.Delete("Library/ScriptAssemblies/Assembly-CSharp.pdb");
        AssetDatabase.DeleteAsset("Assets/PilotProbe");
        AssetDatabase.Refresh();
    }

    static void Run(string line)
    {
        var space = line.IndexOf(' ');
        var command = space < 0 ? line : line.Substring(0, space);
        var argument = space < 0 ? "" : line.Substring(space + 1);
        switch (command)
        {
            case "reload": Reload(argument, false); break;
            case "reloadp": Reload(argument, true); break;
            case "verify": Verify(); break;
            case "perf": Perf(argument); break;
            case "patch": Patch(argument); break;
            case "hotpatch": HotPatch(argument); break;
            // What the watcher did with a save, shown in the editor (PilotHud.cs).
            case "note": PilotHud.Note(argument); break;
            case "hud": EditorApplication.ExecuteMenuItem("Window/Pilot Hot Reload"); Answer("hud open"); break;
            case "load":
                var loaded = Assembly.Load(File.ReadAllBytes(argument));
                Answer($"loaded {loaded.FullName}");
                // The runtime the patches call; a test's assembly is not kept.
                if (loaded.GetName().Name == "PilotRuntime") SessionState.SetString(LoadsKey, argument);
                break;
            case "call":
            {
                var parts = argument.Split(' ');
                var type = FindType(parts[0]);
                var method = type?.GetMethod(parts[1], BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static,
                    null, Type.EmptyTypes, null);
                Answer(method == null ? $"call: no {argument}" : $"call {argument} = {method.Invoke(null, null)}");
                break;
            }
            case "refresh":
                AssetDatabase.AllowAutoRefresh();
                AssetDatabase.Refresh();
                AssetDatabase.DisallowAutoRefresh();
                Answer("refreshed");
                break;
            // Play Mode, where the game's own code runs: what JIT-compiling
            // every method one by one does not reach — the generic
            // instantiations the game makes as it goes.
            case "play":
            {
                // The game starts from the first scene of the build, which is
                // not what a windowless editor opens.
                var first = EditorBuildSettings.scenes.FirstOrDefault(scene => scene.enabled)?.path;
                if (first != null) UnityEditor.SceneManagement.EditorSceneManager.OpenScene(first);
                EditorApplication.isPlaying = true;
                Answer($"playing {first}");
                break;
            }
            case "stop": EditorApplication.isPlaying = false; Answer("stopped"); break;
            case "hold":
                if (argument == "on") File.WriteAllText(Heartbeat, "");
                Hold(argument == "on");
                Answer($"hold {(holding ? "on" : "off")}");
                break;
            case "state": Answer($"state playing={EditorApplication.isPlaying} compiling={compilingNow} holding={holding}"); break;
            case "quit": EditorApplication.Exit(0); break;
            default: Answer($"unknown {line}"); break;
        }
    }

    static void Reload(string path, bool partial)
    {
        if (compilingNow)
        {
            deferredReload = (path, partial);
            Answer("reload waits for Unity's compile to finish");
            return;
        }
        var begun = DateTime.UtcNow;
        var target = "Library/ScriptAssemblies/Assembly-CSharp.dll";
        // A new file moved into place, not the old one written over: Mono
        // has the old one mapped.
        var staged = target + ".pilot";
        File.Copy(path, staged, true);
        File.Delete(target + ".pdb");
        File.Move(target, target + ".previous");
        File.Move(staged, target);
        File.Delete(target + ".previous");
        SessionState.SetString(StartedKey, begun.Ticks.ToString());
        Answer($"reloading {path} ({new FileInfo(target).Length} bytes)");
        // Our own reload goes through; the new domain holds again.
        if (holding) { EditorApplication.UnlockReloadAssemblies(); holding = false; }
        if (partial)
        {
            // Unity's own, not public: a reload that skips the asset pipeline's
            // pass over every asset.
            typeof(EditorUtility).GetMethod("RequestPartialScriptReload",
                BindingFlags.Static | BindingFlags.NonPublic | BindingFlags.Public).Invoke(null, null);
        }
        else
        {
            EditorUtility.RequestScriptReload();
        }
    }

    static void Verify()
    {
        var watch = Stopwatch.StartNew();
        File.Delete(Path.Combine(Directory, "failures.txt"));
        var assembly = GameAssembly();
        if (assembly == null) { Answer("verify: no Assembly-CSharp loaded"); return; }
        Type[] types;
        var typeErrors = new List<string>();
        try { types = assembly.GetTypes(); }
        catch (ReflectionTypeLoadException error)
        {
            types = error.Types.Where(type => type != null).ToArray();
            typeErrors.AddRange(error.LoaderExceptions.Select(e => e.Message).Distinct());
        }
        int methods = 0, jitted = 0;
        var failures = new Dictionary<string, List<string>>();
        const BindingFlags all = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance
            | BindingFlags.Static | BindingFlags.DeclaredOnly;
        foreach (var type in types)
        {
            if (type.ContainsGenericParameters) continue;
            MethodBase[] members;
            try
            {
                members = type.GetMethods(all).Cast<MethodBase>()
                    .Concat(type.GetConstructors(all)).ToArray();
            }
            catch (Exception error) { Note(failures, error, type.FullName); continue; }
            foreach (var method in members)
            {
                if (method.IsAbstract || method.ContainsGenericParameters) continue;
                if ((method.MethodImplementationFlags & MethodImplAttributes.InternalCall) != 0) continue;
                if (method.GetMethodBody() == null) continue;
                methods++;
                try
                {
                    // Mono's PrepareMethod does not compile anything; asking
                    // for the code's address does.
                    if (method.MethodHandle.GetFunctionPointer() != IntPtr.Zero) jitted++;
                }
                catch (Exception error) { Note(failures, error, $"{type.FullName}::{method.Name}"); }
            }
        }
        var scripts = MonoImporter.GetAllRuntimeMonoScripts()
            .Where(script => script != null && AssetDatabase.GetAssetPath(script).StartsWith("Assets/"))
            .ToArray();
        var lost = scripts.Where(script => script.GetClass() == null
            && script.text.Contains("MonoBehaviour")).Select(AssetDatabase.GetAssetPath).ToArray();
        Answer($"verify {watch.ElapsedMilliseconds}ms assembly={Describe(assembly)} types={types.Length} "
            + $"typeErrors={typeErrors.Count} methods={methods} jitted={jitted} "
            + $"failed={methods - jitted} scriptsWithoutClass={lost.Length}");
        foreach (var message in typeErrors.Take(20)) Answer($"  type: {message}");
        foreach (var group in failures.OrderByDescending(group => group.Value.Count).Take(20))
            Answer($"  {group.Value.Count} × {group.Key}: {string.Join("; ", group.Value.Take(3))}");
        foreach (var path in lost.Take(20)) Answer($"  no class: {path}");
    }

    // Native, so that nothing managed runs while JIT memory is writable and
    // therefore not executable (see pilotpatch.c beside the patches).
    // Built from pilotpatch.c (`clang -O2 -dynamiclib -arch arm64 -arch x86_64
    // -o libpilotpatch.dylib pilotpatch.c`) and put beside the probe, where
    // Unity loads it as an editor plugin.
    [System.Runtime.InteropServices.DllImport("pilotpatch")]
    static extern int pilot_write_jump(IntPtr at, IntPtr target);

    static readonly List<Assembly> patches = new List<Assembly>();

    // The first instructions of the method Mono compiled become a jump to
    // the patch's: `ldr x16, #8; br x16; .quad target`. JIT memory on Apple
    // silicon is writable only on a thread that has asked for it, and the
    // instruction cache has to be told the code changed.
    static void Patch(string argument)
    {
        var watch = Stopwatch.StartNew();
        var parts = argument.Split(' ');
        var patch = Assembly.Load(File.ReadAllBytes(parts[0]));
        patches.Add(patch);
        const BindingFlags all = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static | BindingFlags.Instance;
        var original = FindType(parts[1]).GetMethod(parts[2], all);
        var replacement = patch.GetType(parts[1]).GetMethod(parts[2], all);
        var from = original.MethodHandle.GetFunctionPointer();
        var to = replacement.MethodHandle.GetFunctionPointer();
        pilot_write_jump(from, to);
        Answer($"patched {parts[1]}::{parts[2]} {from.ToInt64():X} -> {to.ToInt64():X} in {watch.Elapsed.TotalMilliseconds:F1} ms");
    }

    static void HotPatch(string path)
    {
        var watch = Stopwatch.StartNew();
        var patch = Assembly.Load(File.ReadAllBytes(path));
        patches.Add(patch);
        const BindingFlags all = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static
            | BindingFlags.Instance | BindingFlags.DeclaredOnly;
        var done = new List<string>();
        var skipped = new List<string>();
        // `!run` lines are run once the jumps are in: a static field given the
        // value its changed initializer says, a changed static constructor.
        var runs = new List<(string what, MethodInfo method)>();
        foreach (var line in File.ReadAllLines(Path.ChangeExtension(path, ".txt")))
        {
            if (line.Length == 0) continue;
            var parts = line.Split('\t');
            if (parts[0] == "!run")
            {
                runs.Add((parts[1], patch.GetType(parts[3])?.GetMethod(parts[4], all)));
                continue;
            }
            var names = parts[2].Length == 0 ? new string[0] : parts[2].Split(',');
            var type = FindType(parts[0]);
            var original = type?.GetMethods(all).Cast<MethodBase>()
                .Concat(type.GetConstructors(all))
                .FirstOrDefault(method => method.Name == parts[1]
                    && method.GetParameters().Select(parameter => parameter.ParameterType.Name).SequenceEqual(names));
            var replacement = patch.GetType(parts[3])?.GetMethod(parts[4], all);
            if (original == null || replacement == null)
            {
                Answer($"hotpatch: cannot find {(original == null ? parts[0] + "::" + parts[1] : parts[3] + "::" + parts[4])}");
                continue;
            }
            IntPtr from, to;
            try
            {
                from = original.MethodHandle.GetFunctionPointer();
                to = replacement.MethodHandle.GetFunctionPointer();
            }
            catch (TypeInitializationException error)
            {
                // Compiling the method runs its type's static constructor,
                // and this one throws in the editor (a native plugin of
                // another platform, say): the method cannot run here either
                // way, and the rest of the patch still goes in.
                skipped.Add($"{parts[0]}::{parts[1]} ({error.InnerException?.GetType().Name ?? "type initializer"})");
                continue;
            }
            pilot_write_jump(from, to);
            done.Add($"{parts[0]}::{parts[1]}");
        }
        foreach (var (what, method) in runs)
        {
            if (method == null) { Answer($"hotpatch: cannot find what runs {what}"); continue; }
            method.Invoke(null, null);
            done.Add($"ran {what}");
        }
        var notes = skipped.Count == 0 ? "" : $"; skipped, their type does not initialize in the editor: {string.Join(", ", skipped)}";
        Answer($"hotpatched {done.Count} in {watch.Elapsed.TotalMilliseconds:F1} ms: {string.Join(", ", done)}{notes}");
    }

    static void Perf(string argument)
    {
        var floor = argument.Length > 0 ? double.Parse(argument) : 20;
        var trackers = typeof(EditorApplication).Assembly.GetType("UnityEditor.Profiling.EditorPerformanceTracker");
        var all = (string[])trackers.GetMethod("GetAvailableTrackers").Invoke(null, null);
        var last = trackers.GetMethod("GetLastTime");
        var stamp = trackers.GetMethod("GetTimestamp");
        var rows = all
            .Select(name => (name, ms: (double)last.Invoke(null, new object[] { name }), at: (double)stamp.Invoke(null, new object[] { name })))
            .Where(row => row.ms >= floor)
            .OrderByDescending(row => row.at)
            .Take(60);
        foreach (var row in rows) Answer($"  perf {row.ms,8:F1} ms  at {row.at:F2}  {row.name}");
        Answer($"perf done (now {EditorApplication.timeSinceStartup:F2})");
    }

    static void Note(Dictionary<string, List<string>> failures, Exception error, string where)
    {
        while (error is TargetInvocationException && error.InnerException != null) error = error.InnerException;
        var key = error.GetType().Name + ": " + Shorten(error.Message);
        if (!failures.TryGetValue(key, out var list)) failures[key] = list = new List<string>();
        list.Add(where);
        var detail = error.ToString().Replace("\n", " | ");
        File.AppendAllText(Path.Combine(Directory, "failures.txt"), $"{where}\t{detail}\n");
    }

    static string Shorten(string text) => text.Length > 160 ? text.Substring(0, 160) + "…" : text;

    // A type of Assembly-CSharp, or of any other assembly loaded but the
    // patches, which declare the same names.
    static Type FindType(string name) =>
        GameAssembly()?.GetType(name)
        ?? AppDomain.CurrentDomain.GetAssemblies()
            .Where(assembly => !patches.Contains(assembly))
            .Select(assembly => assembly.GetType(name))
            .FirstOrDefault(type => type != null);

    static Assembly GameAssembly() => AppDomain.CurrentDomain.GetAssemblies()
        .FirstOrDefault(assembly => assembly.GetName().Name == "Assembly-CSharp");

    static string Describe(Assembly assembly)
    {
        if (assembly == null) return "none";
        var location = assembly.Location;
        var size = location.Length > 0 && File.Exists(location) ? new FileInfo(location).Length : -1;
        return $"{assembly.ManifestModule.ModuleVersionId} ({size} bytes)";
    }

    static void Answer(string line)
    {
        var stamped = $"{DateTime.Now:HH:mm:ss.fff} {line}";
        File.AppendAllText(Log, stamped + "\n");
        // The editor's Console is the game's: routine answers stay in the
        // log the patching editor reads, and only what went wrong shows there.
        if (line.StartsWith("failed") || line.Contains("Exception"))
            Debug.LogFormat(LogType.Warning, LogOption.NoStacktrace, null, "[PilotProbe] {0}", line);
    }
}
