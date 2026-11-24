#!/usr/bin/env python3
"""Every recent commit of a project replayed as edits on its own parent.

For each commit that touches Assembly-CSharp, oldest first: the project's
C# as it was just before it, with what the source generators write for it,
is built whole by the daemon — that is what the editor would have loaded —
and then the commit's files are saved one after another, as edits, and the
daemon answers each with a patch or why a reload is needed. The last answer
is the commit's.

The repository is only read (`git show`, `git diff`, `git archive`): the C#
goes into a directory of its own, moved from commit to commit. The
references (other assemblies, packages) and the generators are the ones the
experimental copy has now.

usage: history.py <repository> <count of commits> <work directory>
environment: RUSTLYN_UNITY_PROJECT (the experimental copy), RUSTLYN_SCRATCH
(where `rl/refs`, `rl/defines.txt`, `csc/args.rsp` and the runtime are),
RUSTLYN (the rustlyn checkout), MINIGEN and GEND2 (their built dlls)
"""
import io
import os
import re
import shutil
import subprocess
import sys
import tarfile
import time

COPY = os.environ["RUSTLYN_UNITY_PROJECT"]
SCRATCH = os.environ["RUSTLYN_SCRATCH"]
RUSTLYN = os.environ["RUSTLYN"]
MINIGEN = os.environ["MINIGEN"]
GEND = os.environ["GEND2"]
CONTEXT = r"UpdateMiddleware\(|InjectionResolver\("


def git(repository, *arguments):
    return subprocess.run(["git", "-C", repository, *arguments], capture_output=True, check=False).stdout


class Membership:
    """Whether a path is a source of Assembly-CSharp: as the build has it now,
    or, for a file the project no longer has, as most of its folder's files
    are."""

    def __init__(self, members, everything):
        self.members = set(members)
        self.everything = set(everything)
        self.folders = {}
        for path in self.everything:
            folder = os.path.dirname(path)
            yes, no = self.folders.get(folder, (0, 0))
            self.folders[folder] = (yes + 1, no) if path in self.members else (yes, no + 1)

    def __call__(self, path):
        if not path.startswith("Assets/") or not path.endswith(".cs"):
            return False
        if path in self.members:
            return True
        if path in self.everything:
            return False
        folder = os.path.dirname(path)
        while folder:
            if folder in self.folders:
                yes, no = self.folders[folder]
                return yes > no
            folder = os.path.dirname(folder)
        return False


class Process:
    """A daemon spoken to a line at a time."""

    def __init__(self, command, directory, log):
        self.log = open(log, "a", encoding="utf-8", buffering=1)
        self.process = subprocess.Popen(command, cwd=directory, stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                        text=True, bufsize=1, start_new_session=True)

    def send(self, line):
        self.process.stdin.write(line + "\n")
        self.process.stdin.flush()

    def until(self, pattern):
        while True:
            line = self.process.stdout.readline()
            if not line:
                raise RuntimeError(f"the daemon ended, waiting for {pattern}")
            self.log.write(line)
            if re.search(pattern, line):
                return line.rstrip("\n")

    def stop(self):
        try:
            self.send("quit")
            self.process.stdin.close()
            self.process.wait(timeout=30)
        except Exception:
            self.process.kill()


def main():
    repository, count, work = sys.argv[1], int(sys.argv[2]), os.path.abspath(sys.argv[3])
    project = os.path.join(work, "project")
    generated = os.path.join(work, "gen")
    hot = os.path.join(work, "hot")
    for directory in (work, generated, hot):
        os.makedirs(directory, exist_ok=True)
    report_path = os.path.join(work, "report.tsv")

    rsp_now = open(os.path.join(SCRATCH, "csc/args.rsp"), encoding="utf-8").read().splitlines()
    members_now = [line.strip().strip('"') for line in rsp_now
                   if line.strip().strip('"').startswith("Assets/") and line.strip().strip('"').endswith(".cs")]
    everything_now = git(repository, "ls-files", "--", "*.cs").decode().splitlines()
    member = Membership(members_now, everything_now)

    def absolute(value):
        return value if os.path.isabs(value) else os.path.join(COPY, value)

    # The response file the generators read: the build's, with its paths made
    # absolute and its sources those of the state at hand.
    options = []
    for line in rsp_now:
        entry = line.strip()
        bare = entry.strip('"')
        if bare.endswith(".cs") and not entry.startswith(("-", "/")):
            continue
        for prefix in ("-r:", "-analyzer:", "/additionalfile:"):
            if entry.startswith(prefix):
                entry = prefix + '"' + absolute(entry[len(prefix):].strip('"')) + '"'
        options.append(entry)

    listed = git(repository, "log", "--no-merges", "--format=%H", f"-n{count}", "--", "*.cs").decode().split()
    commits = []
    for commit in reversed(listed):
        changed = git(repository, "diff-tree", "--no-commit-id", "--name-status", "--no-renames", "-r",
                      commit, "--", "*.cs").decode().splitlines()
        files = [(item.split("\t")[0][0], item.split("\t")[-1]) for item in changed]
        if any(member(path) for _, path in files):
            commits.append((commit, files))
    # `HISTORY_ONLY=abc123,def456` replays only those, each from scratch.
    only = [prefix for prefix in os.environ.get("HISTORY_ONLY", "").split(",") if prefix]
    if only:
        commits = [(commit, files) for commit, files in commits if any(commit.startswith(p) for p in only)]
    print(f"{len(commits)} of {len(listed)} commits touch Assembly-CSharp", flush=True)

    done = set()
    if os.path.exists(report_path):
        done = {line.split("\t")[0] for line in open(report_path, encoding="utf-8")}

    state = None
    gend = None
    for number, (commit, files) in enumerate(commits, 1):
        if commit[:10] in done:
            continue
        started = time.time()
        parent = commit + "^"
        # The C# as it was before the commit.
        if state is None:
            shutil.rmtree(project, ignore_errors=True)
            os.makedirs(project)
            archive = git(repository, "archive", parent, "--", "*.cs")
            with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
                tar.extractall(project)
            edits = None
        else:
            moved = git(repository, "diff", "--name-status", "--no-renames", state, parent, "--", "*.cs").decode().splitlines()
            edits = []
            for item in moved:
                status, path = item.split("\t")[0][0], item.split("\t")[-1]
                full = os.path.join(project, path)
                if status == "D":
                    if os.path.exists(full):
                        os.remove(full)
                    if member(path):
                        edits.append("- " + path)
                    continue
                os.makedirs(os.path.dirname(full), exist_ok=True)
                with open(full, "wb") as file:
                    file.write(git(repository, "show", f"{parent}:{path}"))
                if member(path):
                    edits.append(path)
        state = parent
        sources = sorted(path for path in (
            os.path.relpath(os.path.join(root, name), project)
            for root, _, names in os.walk(os.path.join(project, "Assets")) for name in names if name.endswith(".cs"))
            if member(path))

        # What the generators write for it. Moved from state to state, they
        # can trip over trees they kept from the one before ("not part of
        # the compilation"); then they start again on this state alone.
        def fresh():
            rsp = os.path.join(work, "args.rsp")
            with open(rsp, "w", encoding="utf-8") as file:
                file.write("\n".join(options + [f'"{path}"' for path in sources]) + "\n")
            shutil.rmtree(generated, ignore_errors=True)
            started_generators = Process(["dotnet", GEND, rsp, project, generated], project,
                                         os.path.join(work, "gend.log"))
            return started_generators, started_generators.until(r"^ready")

        if gend is None:
            gend, generators_said = fresh()
        else:
            for edit in edits:
                gend.send(edit)
            gend.send("run")
            generators_said = gend.until(r"^generated")
            if "threw:" in generators_said:
                gend.stop()
                gend, generators_said = fresh()
        # A generator that threw on this state kept what it wrote before: the
        # state's build is then only nearly what the editor had.
        threw = "threw" if "threw:" in generators_said else ""
        made = sorted(os.path.join(root, name) for root, _, names in os.walk(generated) for name in names
                      if name.endswith(".cs"))
        source_list = os.path.join(work, "sources.txt")
        with open(source_list, "w", encoding="utf-8") as file:
            file.write("\n".join(sources + made) + "\n")
        before = set(made)

        # The editor's build of it, and the commit saved file by file.
        out = os.path.join(work, "Assembly-CSharp.dll")
        generators = (f"dotnet {MINIGEN} {os.path.join(work, 'args.rsp')} {project} {generated} {out} "
                      f"'{CONTEXT}' {source_list}")
        serve = Process([os.path.join(RUSTLYN, "target/release/examples/serve"), os.path.join(SCRATCH, "rl/refs"),
                         out, "--define", open(os.path.join(SCRATCH, "rl/defines.txt")).read().strip(),
                         "--sources", source_list, "--hot", hot,
                         "--runtime", os.path.join(SCRATCH, "serve/runtime/PilotRuntime.dll"),
                         "--generators", generators], project, os.path.join(work, "serve.log"))
        verdict, why, stubs = "error", "", ""
        try:
            ready = serve.until(r"^ready ")
            stubs = re.search(r"(\d+) stubs", ready).group(1)
            serve.until(r"^generators ")
            built = time.time() - started
            answers = []
            for status, path in files:
                full = os.path.join(project, path)
                if status == "D":
                    if os.path.exists(full):
                        os.remove(full)
                    continue
                os.makedirs(os.path.dirname(full), exist_ok=True)
                with open(full, "wb") as file:
                    file.write(git(repository, "show", f"{commit}:{path}"))
            # New files first, as they are made before what uses them.
            for status, path in sorted(files, key=lambda entry: entry[0] != "A"):
                if status == "D" or not member(path):
                    continue
                serve.send(path)
                answer = serve.until(r"^(patch|nopatch|refused|unchanged) ")
                if not answer.startswith("refused"):
                    serve.until(r"^(rebuilt|stale|unchanged) ")
                answers.append(answer)
            # Once more, now that the generators have seen every file of the
            # commit: a feature saved before the system it gains is written
            # again knowing it.
            for status, path in files:
                if status == "D" or not member(path):
                    continue
                serve.send(path)
                answer = serve.until(r"^(patch|nopatch|refused|unchanged) ")
                if not answer.startswith("refused"):
                    serve.until(r"^(rebuilt|stale|unchanged) ")
                answers.append(answer)
            last = answers[-1] if answers else "unchanged nothing of Assembly-CSharp kept"
            verdict = {"patch": "patch", "unchanged": "patch", "nopatch": "reload", "refused": "reload"}[last.split()[0]]
            why = "" if verdict == "patch" else last.split(" ", 1)[1]
            # A commit whose files do not compile here — broken as committed,
            # or needing what a package had then — says nothing of patching.
            if verdict == "reload":
                for status, path in files:
                    if status == "D" or not member(path):
                        continue
                    serve.send(f"errors {path}")
                    said = serve.until(r"^errors \d+ ")
                    if int(said.split()[1]) > 0:
                        verdict, why = "broken", said
                        break
            timing = re.search(r"^patch (\d+) ms", last)
            took = timing.group(1) if timing else ""
        except Exception as error:
            why, built, took = str(error), 0, ""
        finally:
            serve.stop()
        kept = os.path.join(work, "patches", commit[:10])
        os.makedirs(kept, exist_ok=True)
        for name in os.listdir(hot):
            shutil.move(os.path.join(hot, name), os.path.join(kept, name))
        state = commit
        # What the patch rounds' generators wrote goes; the generators' own
        # run for the next state writes back what they changed.
        for root, _, names in os.walk(generated):
            for name in names:
                path = os.path.join(root, name)
                if path not in before:
                    os.remove(path)

        lines = sum(int(a) + int(b) for a, b, *_ in (
            row.split("\t") for row in git(repository, "show", "--format=", "--numstat", commit, "--", "*.cs")
            .decode().splitlines()) if a.isdigit() and b.isdigit())
        subject = git(repository, "log", "-1", "--format=%cs %s", commit).decode().strip()
        row = [commit[:10], verdict, str(len(files)), str(lines), stubs, f"{built:.0f}", took,
               why.replace("\t", " ")[:400], subject[:120], threw]
        with open(report_path, "a", encoding="utf-8") as report:
            report.write("\t".join(row) + "\n")
        print(f"{number}/{len(commits)} {commit[:10]} {verdict:6} {lines:4} lines {stubs:>4} stubs {threw:5} "
              f"{time.time() - started:4.0f}s {why[:120]}", flush=True)
    if gend:
        gend.stop()


main()
