#!/usr/bin/env python3
"""Times rustlyn and csc on the same input, measured the same way.

Both compilers are given the same files, the same framework and the same
`/define:` set, and both are asked for the same thing: one assembly, no
optimisation, no debug information. What comes out is wall time, processor
time (which says how much of the wall time was parallelism) and peak memory.

    tools/bench/run.py --dotnet ~/dotnet --roslyn ~/roslyn [--repeat 3]

The corpora are Roslyn's own sources, in three sizes, so the numbers say
something about how each compiler scales rather than only about one input.
"""

import argparse
import json
import os
import pathlib
import resource
import shutil
import subprocess
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent

# What the SDK defines for a `net11.0` project, which is what Roslyn's own
# build targets. Without them a file takes a branch nobody compiles.
DEFINES = ";".join(
    ["NET", "NETCOREAPP", "NET11_0"]
    + ["NET%d_0_OR_GREATER" % n for n in range(11, 4, -1)]
    + ["NETCOREAPP3_1_OR_GREATER", "NETCOREAPP3_0_OR_GREATER"]
    + ["NETCOREAPP2_2_OR_GREATER", "NETCOREAPP2_1_OR_GREATER", "NETCOREAPP2_0_OR_GREATER"]
    + ["NETCOREAPP1_1_OR_GREATER", "NETCOREAPP1_0_OR_GREATER"]
)


# A process of its own around each run, so that the kernel's accounting for
# children is about that run alone: `ru_maxrss` is the high-water mark over
# every child a process has ever had, and one compiler's peak would otherwise
# be reported as the next one's.
WRAPPER = """
import resource, subprocess, sys
done = subprocess.run(sys.argv[1:])
used = resource.getrusage(resource.RUSAGE_CHILDREN)
sys.stderr.write("\\nmeasured %r\\n" % ((used.ru_utime + used.ru_stime, used.ru_maxrss, done.returncode),))
"""


def run(command, stdin=None, env=None):
    """Runs a command, returning wall seconds, processor seconds and peak KiB."""
    started = time.monotonic()
    with open(stdin) if stdin else open(os.devnull) as handle:
        done = subprocess.run(
            [sys.executable, "-c", WRAPPER] + list(command),
            stdin=handle, capture_output=True, text=True,
            env=dict(os.environ, **env) if env else None,
        )
    wall = time.monotonic() - started
    cpu, peak, code = 0.0, 0, done.returncode
    for line in done.stderr.splitlines():
        if line.startswith("measured "):
            cpu, peak, code = eval(line[len("measured "):])
    return {
        "wall": wall,
        "cpu": cpu,
        "peak_kib": peak,
        "code": code,
        "out": done.stdout,
        "err": done.stderr,
    }


def best(runs, key="wall"):
    return min(runs, key=lambda measured: measured[key])


def corpora(roslyn, generated):
    """The three inputs, smallest first."""
    compilers = roslyn / "src" / "Compilers"
    dependencies = roslyn / "src" / "Dependencies"
    core = [compilers / "Core" / "Portable", compilers / "Core" / "AnalyzerDriver"]
    csharp = [compilers / "CSharp" / "Portable", compilers / "CSharp" / "CSharpAnalyzerDriver"]

    def files(directories):
        found = []
        for directory in directories:
            found.extend(sorted(str(p) for p in pathlib.Path(directory).rglob("*.cs")))
        return found

    resources = [str(generated / "CodeAnalysisResources.cs"), str(generated / "CSharpResources.cs")]
    regex = [str(HERE / "generated" / "AnalyzerConfig.RegexGenerator.g.cs")]
    # One file, to see what each compiler costs before it has read anything:
    # a native binary starts, a compiler on a virtual machine has itself to
    # load and to compile first.
    hello = generated / "Hello.cs"
    hello.write_text(
        "using System;\n\nclass Hello\n{\n"
        "    static void Main() { Console.WriteLine(\"hi\"); }\n}\n"
    )
    return [
        ("hello", [str(hello)]),
        ("dependencies", files([dependencies])),
        ("core", files([dependencies] + core) + resources[:1] + regex),
        ("everything", files([dependencies] + core + csharp) + resources + regex),
    ]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--dotnet", default=os.environ.get("DOTNET", str(pathlib.Path.home() / "dotnet")))
    parser.add_argument("--roslyn", default=os.environ.get("ROSLYN", str(pathlib.Path.home() / "roslyn")))
    parser.add_argument("--repeat", type=int, default=3)
    parser.add_argument("--framework", default=None, help="a Microsoft.NETCore.App directory; the newest by default")
    parser.add_argument("--work", default=None, help="where to put the corpus lists and the assemblies")
    parser.add_argument("--only", default=None, help="run one corpus by name")
    parser.add_argument("--json", default=None, help="write the measurements here as well")
    parser.add_argument("--shared", action="store_true",
                        help="also time csc against a warm VBCSCompiler, the way MSBuild runs it")
    arguments = parser.parse_args()

    dotnet_root = pathlib.Path(arguments.dotnet)
    dotnet = dotnet_root / "dotnet"
    roslyn = pathlib.Path(arguments.roslyn)
    work = pathlib.Path(arguments.work or (ROOT / "target" / "bench"))
    work.mkdir(parents=True, exist_ok=True)
    (work / "out").mkdir(exist_ok=True)

    def version(path):
        # `11.0.0-rc.1` sorts before `8.0.31` as text and after it as a
        # version, and the corpus only compiles against the newer one.
        head = path.name.split("-")[0]
        return tuple(int(part) if part.isdigit() else 0 for part in head.split("."))

    frameworks = sorted((dotnet_root / "shared" / "Microsoft.NETCore.App").glob("*"), key=version)
    if not frameworks:
        sys.exit("no Microsoft.NETCore.App under %s" % dotnet_root)
    framework = pathlib.Path(arguments.framework) if arguments.framework else frameworks[-1]
    cscs = sorted(dotnet_root.glob("sdk/*/Roslyn/bincore/csc.dll"))
    if not cscs:
        sys.exit("no csc.dll under %s/sdk; install an SDK to compare against" % dotnet_root)
    csc = cscs[-1]

    assemble = ROOT / "target" / "release" / "examples" / "assemble"
    resx = ROOT / "target" / "release" / "examples" / "resx"
    if not assemble.exists() or not resx.exists():
        sys.exit("build first: cargo build --release --examples")

    # The two classes the real build makes from `.resx` with a generator out of
    # a NuGet package. Without them 287 references across the corpus reach a
    # name nothing declares, so both compilers are given them.
    generated = work / "generated"
    generated.mkdir(exist_ok=True)
    for namespace, source, name in [
        ("Microsoft.CodeAnalysis", "Core/Portable/CodeAnalysisResources.resx", "CodeAnalysisResources.cs"),
        ("Microsoft.CodeAnalysis.CSharp", "CSharp/Portable/CSharpResources.resx", "CSharpResources.cs"),
    ]:
        made = subprocess.run(
            [str(resx), namespace, str(roslyn / "src" / "Compilers" / source)],
            capture_output=True, text=True, check=True,
        )
        (generated / name).write_text(made.stdout)

    print("csc       %s" % subprocess.run([str(dotnet), str(csc), "-version"], capture_output=True, text=True).stdout.strip())
    print("framework %s" % framework.name)
    print("rustlyn   %s" % subprocess.run(["git", "-C", str(ROOT), "log", "-1", "--format=%h %s"], capture_output=True, text=True).stdout.strip()[:60])
    print("machine   %d cores" % os.cpu_count())
    print()

    measurements = []
    for name, files in corpora(roslyn, generated):
        if arguments.only and name != arguments.only:
            continue
        listing = work / ("%s.txt" % name)
        listing.write_text("\n".join(files) + "\n")
        lines = sum(1 for path in files for _ in open(path, encoding="utf-8", errors="replace"))

        rsp = work / ("%s.rsp" % name)
        with open(rsp, "w") as out:
            print("/nullable:annotations", file=out)
            print("/nowarn:RSEXPERIMENTAL006,CS8632,CS1591,CS0649,CS0169", file=out)
            print("/nostdlib+", file=out)
            print("/target:library", file=out)
            print("/out:%s" % (work / "out" / ("%s-csc.dll" % name)), file=out)
            print("/define:%s" % DEFINES, file=out)
            print("/unsafe+", file=out)
            print("/langversion:preview", file=out)
            print("/nologo", file=out)
            print("/optimize-", file=out)
            print("/debug-", file=out)
            print("/deterministic+", file=out)
            for reference in sorted(framework.glob("*.dll")):
                print("/r:%s" % reference, file=out)
            for path in files:
                print('"%s"' % path, file=out)

        wrote = work / "out" / ("%s-rustlyn.dll" % name)
        # No `--resource`: csc cannot read a `.resx` and Roslyn's build runs a
        # generator over them first, so embedding the strings would be work
        # one compiler does and the other does not.
        rustlyn_command = [str(assemble), str(framework), str(wrote), "--define", DEFINES]

        for label, command, stdin in [
            ("csc", [str(dotnet), str(csc), "/noconfig", "@%s" % rsp], None),
            ("rustlyn", rustlyn_command, listing),
        ]:
            runs = [run(command, stdin) for _ in range(arguments.repeat)]
            fastest = best(runs)
            errors = [line for line in (fastest["out"] + fastest["err"]).splitlines() if ": error " in line]
            produced = work / "out" / ("%s-%s.dll" % (name, label))
            measurements.append({
                "corpus": name, "compiler": label, "files": len(files), "lines": lines,
                "wall": fastest["wall"], "cpu": fastest["cpu"], "peak_mib": fastest["peak_kib"] / 1024.0,
                "bytes": produced.stat().st_size if produced.exists() else 0,
                "errors": len(errors), "first_error": errors[0] if errors else "",
            })
            print("%-11s %-8s %6.2f s wall  %6.2f s cpu  %6.0f MiB  %8d bytes%s"
                  % (name, label, fastest["wall"], fastest["cpu"],
                     fastest["peak_kib"] / 1024.0, measurements[-1]["bytes"],
                     "  %d errors" % len(errors) if errors else ""))
            if errors:
                print("            %s" % errors[0][:150])

        if arguments.shared:
            # How MSBuild actually runs csc: `/shared` hands the work to a
            # VBCSCompiler that outlives the build. Nothing here is a child of
            # the process we time, so only the wall clock means anything —
            # the processor time and the peak belong to the server.
            #
            # The server has to find its own host to start at all, and inside
            # a container `dotnet` is often not on PATH as something it can
            # resolve; without this it fails to start, the client waits out
            # its 20-second connect timeout and compiles in-process anyway.
            server = {"DOTNET_HOST_PATH": str(dotnet), "PATH": "%s%s%s" % (dotnet_root, os.pathsep, os.environ.get("PATH", ""))}
            command = [str(dotnet), str(csc), "/noconfig", "/shared", "@%s" % rsp]
            # The first calls through a fresh server are still being JIT-ed,
            # and on this corpus that is worth a factor of three. Warm it up
            # and throw those away.
            for _ in range(arguments.repeat):
                run(command, env=server)
            fastest = best([run(command, env=server) for _ in range(arguments.repeat)])
            measurements.append({
                "corpus": name, "compiler": "csc+server", "files": len(files), "lines": lines,
                "wall": fastest["wall"], "cpu": 0.0, "peak_mib": 0.0,
                "bytes": 0, "errors": 0, "first_error": "",
            })
            print("%-11s %-8s %6.2f s wall" % (name, "csc+server", fastest["wall"]))
        print()

    served = " csc+server |" if arguments.shared else ""
    print("| corpus | files | lines | csc |%s rustlyn | csc CPU | rustlyn CPU | csc RSS | rustlyn RSS |"
          % served)
    print("| --- | ---: | ---: | ---: |%s ---: | ---: | ---: | ---: | ---: |" % (" ---: |" if arguments.shared else ""))
    for name in dict.fromkeys(m["corpus"] for m in measurements):
        pair = {m["compiler"]: m for m in measurements if m["corpus"] == name}
        if "csc" not in pair or "rustlyn" not in pair:
            continue
        print("| %s | %d | %d | %.2f s |%s %.2f s | %.1f s | %.1f s | %.0f MiB | %.0f MiB |" % (
            name, pair["csc"]["files"], pair["csc"]["lines"], pair["csc"]["wall"],
            (" %.2f s |" % pair["csc+server"]["wall"]) if "csc+server" in pair else "",
            pair["rustlyn"]["wall"],
            pair["csc"]["cpu"], pair["rustlyn"]["cpu"],
            pair["csc"]["peak_mib"], pair["rustlyn"]["peak_mib"]))
    print()
    for name in dict.fromkeys(m["corpus"] for m in measurements):
        pair = {m["compiler"]: m for m in measurements if m["corpus"] == name}
        if "csc" not in pair or "rustlyn" not in pair or not pair["csc"]["lines"]:
            continue
        print("%-12s csc %7.0f lines/s (%.1f cores), rustlyn %7.0f lines/s (%.1f cores)" % (
            name,
            pair["csc"]["lines"] / pair["csc"]["wall"], pair["csc"]["cpu"] / pair["csc"]["wall"],
            pair["rustlyn"]["lines"] / pair["rustlyn"]["wall"],
            pair["rustlyn"]["cpu"] / pair["rustlyn"]["wall"]))

    if arguments.json:
        pathlib.Path(arguments.json).write_text(json.dumps(measurements, indent=2))


if __name__ == "__main__":
    main()
