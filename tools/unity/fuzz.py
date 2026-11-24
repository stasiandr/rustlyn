#!/usr/bin/env python3
"""Edits the game's files as a person would, one at a time, through the
daemon into the copy's running editor — and back.

Each case picks a file of Assembly-CSharp and an edit (`examples/mutate`:
a log line, a number, a method, field or nested type added and used, a
condition turned round, spacing, a save in the middle of typing), saves it,
and checks what comes of it:

- a file that does not compile is answered `broken`, and one that does is
  not;
- a patch compiles (`nopatch` with the patch's own compile errors is a bug of
  the patch writer), applies in the editor, and leaves out what only spacing
  touched;
- the edit taken back is patched back as well.

An edit a patch cannot carry is built whole and the editor reloaded on it,
and every so often the editor reloads on a whole build anyway and JITs all
of it (`verify`). One line per case; what failed is kept with its file under
`$RUSTLYN_SERVE_DIR/fuzz/`.

usage: fuzz.py [cases] [first seed]
environment: RUSTLYN_SERVE_DIR, RUSTLYN_UNITY_PROJECT (the serve directory and the Unity project copy),
             RUSTLYN_DEFINES (a file with the defines, `;` between them),
             RUSTLYN_MUTATE (the mutate example), RUSTLYN_FUZZ_KINDS (some kinds only)
"""
import os
import signal
import random
import re
import shutil
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from wake import wake_editor  # noqa: E402

SERVE = os.environ["RUSTLYN_SERVE_DIR"]
PROJECT = os.environ["RUSTLYN_UNITY_PROJECT"]
MUTATE = os.environ["RUSTLYN_MUTATE"]
DEFINES = open(os.environ["RUSTLYN_DEFINES"], encoding="utf-8").read().strip()
# The game running in Play Mode while patches go in: what they change runs,
# and the editor's log is read for what went wrong as it did.
PLAY = bool(os.environ.get("RUSTLYN_FUZZ_PLAY"))
EDITOR_LOG = os.path.expanduser("~/Library/Logs/Unity/Editor.log")
# What only broken code makes the runtime say.
RUNTIME_BROKEN = re.compile(r"InvalidProgramException|MissingMethodException|MissingFieldException|TypeLoadException|"
                            r"BadImageFormatException|ExecutionEngineException|VerificationException|"
                            r"Native Crash|Received signal SIG|\* Assertion")
# Only the daemon: no editor applies or reloads anything.
NO_EDITOR = bool(os.environ.get("RUSTLYN_NO_EDITOR"))
KINDS = [kind for kind in os.environ.get("RUSTLYN_FUZZ_KINDS", "").split(",") if kind]
PROBE = os.path.join(PROJECT, "Temp/PilotProbe")
OUT = os.path.join(SERVE, "out.txt")
CMDS = os.path.join(SERVE, "cmds.txt")
ASSEMBLY = os.path.join(SERVE, "Assembly-CSharp.dll")
RUNTIME = os.path.join(SERVE, "runtime/PilotRuntime.dll")
WORK = os.path.join(SERVE, "fuzz")
ANSWER = r"^(patch|nopatch|refused|unchanged|broken) "
# How many cases bring a new file along.
NEW_FILE_SHARE = float(os.environ.get("RUSTLYN_FUZZ_NEW_FILES", "0.08"))
# How often the editor reloads on a whole build, and is checked whole.
EVERY = 40


def size(path):
    return os.path.getsize(path) if os.path.exists(path) else 0


def wait_line(path, at, pattern, timeout):
    end = time.time() + timeout
    while time.time() < end:
        if os.path.exists(path):
            with open(path, encoding="utf-8", errors="replace") as file:
                file.seek(at)
                for line in file.read().splitlines():
                    if re.search(pattern, line):
                        return line
        time.sleep(0.03)
    return None


def daemon(command, pattern=ANSWER, timeout=120):
    at = size(OUT)
    with open(CMDS, "a") as file:
        file.write(command + "\n")
    return wait_line(OUT, at, pattern, timeout)


def probe(command, pattern, timeout=60):
    log = os.path.join(PROBE, "log.txt")
    at = size(log)
    with open(os.path.join(PROBE, "cmd.txt"), "a") as file:
        file.write(command + "\n")
    line = wait_line(log, at, pattern, timeout)
    if line is None:
        return None
    # What follows the answer's line, indented, belongs to it.
    with open(log, encoding="utf-8", errors="replace") as file:
        file.seek(at)
        lines = file.read().splitlines()
    first = lines.index(line)
    rest = [entry for entry in lines[first + 1:first + 40] if entry.startswith("  ")]
    return "\n".join([re.sub(r"^[0-9:.]+ ", "", line)] + rest)


def daemon_memory():
    """The daemon's resident memory in MB, or 0 when it is not running."""
    found = subprocess.run(["pgrep", "-f", "--", f"--hot {os.path.join(SERVE, 'hot')}"],
                           capture_output=True, text=True).stdout.split()
    if not found:
        return 0
    rss = subprocess.run(["ps", "-o", "rss=", "-p", found[0]], capture_output=True, text=True).stdout.strip()
    return int(rss or 0) // 1024


def editor_alive():
    return bool(subprocess.run(["pgrep", "-f", f"Unity.app/Contents/MacOS/Unity .*-projectPath {PROJECT}"],
                               capture_output=True).stdout)


def log_since(at):
    """The editor's log written since `at`."""
    with open(EDITOR_LOG, encoding="utf-8", errors="replace") as file:
        file.seek(at)
        return file.read()


def play():
    if PLAY:
        probe("play", r"^[0-9:.]+ playing", timeout=120)
        time.sleep(8)


def reload_whole(why):
    """A whole build, the editor reloaded on it, and all of it JITted."""
    if PLAY and not NO_EDITOR:
        probe("stop", r"^[0-9:.]+ stopped", timeout=60)
        time.sleep(2)
        try:
            return reload_whole_stopped(why)
        finally:
            play()
    return reload_whole_stopped(why)


def reload_whole_stopped(why):
    if NO_EDITOR:
        built = daemon("rebuild", r"^(ready |refused the whole build)", timeout=300)
        return "verify typeErrors=0 failed=0 scriptsWithoutClass=0" if built and built.startswith("ready ") \
            else f"whole build: {built or 'no answer'}"
    built = daemon("rebuild", r"^(ready |refused the whole build)", timeout=300)
    if not built or not built.startswith("ready "):
        return f"whole build: {built or 'no answer'}"
    log = os.path.join(PROBE, "log.txt")
    at = size(log)
    with open(os.path.join(PROBE, "cmd.txt"), "a") as file:
        file.write(f"reload {ASSEMBLY}\n")
    time.sleep(0.5)
    wake_editor(PROJECT)
    if not wait_line(log, at, r"^[0-9:.]+ (reloaded|failed)", timeout=600):
        return "the editor did not reload"
    probe(f"load {RUNTIME}", r"^[0-9:.]+ (loaded|failed)")
    verified = probe("verify", r"^[0-9:.]+ verify", timeout=600) or "verify: no answer"
    return verified


def counts(verified):
    found = dict(re.findall(r"(typeErrors|failed|scriptsWithoutClass)=([0-9]+)", verified or ""))
    return {name: int(value) for name, value in found.items()}


def worse_than(verified, baseline):
    """What the whole build does worse than the first one, or None."""
    now, then = counts(verified), counts(baseline)
    if len(now) < 3:
        return verified or "no answer"
    worse = [f"{name} {then.get(name, 0)} → {value}" for name, value in now.items() if value > then.get(name, 0)]
    return ", ".join(worse) or None


def manifest_has(dll, owner, member):
    """Whether the patch replaces `owner`'s `member` (owner as the file names
    it, without a namespace)."""
    with open(dll[:-4] + ".txt", encoding="utf-8") as file:
        for line in file:
            parts = line.split("\t")
            if len(parts) > 1 and (parts[0] == owner or parts[0].endswith("." + owner)
                                   or parts[0].endswith("/" + owner.replace(".", "/"))) and parts[1] == member:
                return True
    return False


def apply(answer):
    """The patch in the editor: None when it went in, else why not."""
    if NO_EDITOR:
        return None
    dll = answer.split()[-1]
    applied = probe(f"hotpatch {dll}", r"^[0-9:.]+ (hotpatched|failed hotpatch)", timeout=60)
    if applied and applied.startswith("hotpatched"):
        return None
    return applied or "no answer from the editor"


def keep(seed, relative, edited, verdict, detail):
    folder = os.path.join(WORK, f"{seed}")
    os.makedirs(folder, exist_ok=True)
    with open(os.path.join(folder, os.path.basename(relative)), "w", encoding="utf-8") as file:
        file.write(edited)
    with open(os.path.join(folder, "what.txt"), "w", encoding="utf-8") as file:
        file.write(f"{relative}\n{verdict}\n{detail}\n")


def main():
    cases = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    first = int(sys.argv[2]) if len(sys.argv) > 2 else int(time.time()) % 100000
    os.makedirs(WORK, exist_ok=True)
    with open(os.path.join(SERVE, "sources.txt"), encoding="utf-8") as file:
        files = [line.strip() for line in file
                 if line.strip().startswith("Assets/") and line.strip().endswith(".cs")
                 and "/Editor/" not in line and os.path.exists(os.path.join(PROJECT, line.strip()))]
    # RUSTLYN_FUZZ_FILES: only these, a comma between each two — the code
    # a scene runs every frame, say.
    if os.environ.get("RUSTLYN_FUZZ_FILES"):
        files = [path for path in os.environ["RUSTLYN_FUZZ_FILES"].split(",") if path]
    chooser = random.Random(first)
    report = open(os.path.join(WORK, "report.tsv"), "a", encoding="utf-8")
    tally = {}
    ran = {"count": 0}
    since_whole = 0
    # What the whole build JITs at the start: a later one may not do worse.
    baseline = reload_whole_stopped("start") if PLAY else reload_whole("start")
    play()
    print("start:", baseline.split("\n")[0], flush=True)
    for case in range(cases):
        seed = first + case
        # Now and then a new file comes with the edit: a class of its own,
        # used where a log line goes; it is deleted again after.
        new_file = chooser.random() < NEW_FILE_SHARE
        # A file with no place for the edit gives way to another.
        for _ in range(50):
            relative = chooser.choice(files)
            path = os.path.join(PROJECT, relative)
            kinds = ["log"] if new_file else ([chooser.choice(KINDS)] if KINDS else [])
            arguments = [MUTATE, path, str(seed)] + kinds + ["--define", DEFINES]
            made = subprocess.run(arguments, capture_output=True, text=True)
            if made.returncode == 0:
                break
        else:
            continue
        kind, owner, member, expect = made.stderr.strip().split("\n")[-1].split("\t")
        with open(path, "rb") as file:
            original = file.read()
        shutil.copy(path, path + ".fuzzkeep")
        started = time.time()
        verdict, detail = "ok", ""
        added = None
        saved = relative
        if new_file:
            added = os.path.join(os.path.dirname(relative), f"FuzzNew{seed}.cs")
            made.stdout = made.stdout.replace(f'"fuzz {seed}"', f"global::FuzzNew{seed}.Value()")
            kind = "new-file"
            saved = f"{relative}\t{added}"
        try:
            with open(path, "w", encoding="utf-8") as file:
                file.write(made.stdout)
            if added:
                with open(os.path.join(PROJECT, added), "w", encoding="utf-8") as file:
                    file.write(f"public static class FuzzNew{seed}\n{{\n    public static int Value() => {seed};\n}}\n")
            answer = daemon(saved) or "none no answer"
            took = time.time() - started
            word = answer.split(" ", 1)[0]
            if expect == "broken":
                if word != "broken":
                    verdict, detail = "BUG not-broken", answer
            elif word == "broken":
                verdict, detail = "invalid", answer
            elif word == "none":
                verdict, detail = "BUG hang", "the daemon did not answer"
            elif word == "nopatch" and "PilotPatch-" in answer and ("error CS" in answer or "did not bind" in answer):
                verdict, detail = "BUG patch-compile", answer
            elif word in ("nopatch", "refused"):
                verdict, detail = "reload", answer
            elif word == "unchanged" and expect == "patch":
                verdict, detail = "BUG unchanged", answer
            elif word == "patch":
                if expect == "spacing" and manifest_has(answer.split()[-1], owner, member):
                    verdict, detail = "BUG spacing-patched", f"{owner}::{member}"
                logged = size(EDITOR_LOG)
                failed = apply(answer)
                if failed:
                    verdict, detail = "BUG apply", failed
                elif PLAY:
                    time.sleep(2.5)
                    said = log_since(logged)
                    broke = RUNTIME_BROKEN.search(said)
                    if broke:
                        start = max(0, broke.start() - 300)
                        verdict, detail = "BUG runtime", said[start:broke.end() + 900]
                    elif re.search(r"Exception.*\n(.*\n){0,12}.*__PilotPatch", said):
                        verdict, detail = "suspect", re.search(r".*Exception.*\n(.*\n){0,12}.*__PilotPatch.*", said).group(0)[:1200]
                    if f"fuzz {seed}" in said or f"one {seed}" in said or f"routine {seed}" in said or f"lambda {seed}" in said:
                        ran["count"] += 1
            if verdict.startswith("BUG") or verdict in ("invalid", "suspect"):
                keep(seed, relative, made.stdout, verdict, detail)
        finally:
            with open(path, "wb") as file:
                file.write(original)
            os.remove(path + ".fuzzkeep")
            if added and os.path.exists(os.path.join(PROJECT, added)):
                os.remove(os.path.join(PROJECT, added))
        # And back: what the edit changed is patched back, or the editor
        # reloads on a whole build.
        back = daemon(saved) or "none no answer"
        whole = verdict == "reload" or not back.startswith(("patch ", "unchanged "))
        if back.startswith("patch "):
            failed = apply(back)
            if failed:
                whole = True
                if not verdict.startswith("BUG"):
                    verdict, detail = "BUG apply-back", failed
        elif not back.startswith("unchanged ") and verdict != "reload" and not (added and "was deleted" in back):
            if not verdict.startswith("BUG"):
                verdict, detail = "BUG back", back
        since_whole += 1
        checked = ""
        if whole or since_whole >= EVERY:
            since_whole = 0
            checked = reload_whole(verdict)
            worse = worse_than(checked, baseline)
            if worse and not verdict.startswith("BUG"):
                verdict, detail = "BUG whole", checked
                keep(seed, relative, made.stdout, verdict, detail)
            checked = " | " + checked.split("\n")[0][:120]
        if not NO_EDITOR and not editor_alive():
            verdict, detail = "BUG editor-died", detail
            keep(seed, relative, made.stdout, verdict, detail)
        memory = daemon_memory()
        if memory == 0 and not verdict.startswith("BUG"):
            verdict, detail = "BUG daemon-died", f"after {relative}"
        tally[verdict] = tally.get(verdict, 0) + 1
        line = f"{case + 1}/{cases}\t{seed}\t{kind}\t{verdict}\t{took:.2f}s\t{relative}\t{owner}::{member}\t{detail[:300]}\t{memory}MB"
        report.write(line.replace("\n", " | ") + "\n")
        report.flush()
        print(f"{case + 1}/{cases} {seed} {kind:16} {verdict:18} {took:5.2f}s "
              f"{memory}MB {os.path.basename(relative)} {detail[:160]}{checked}".replace("\n", " | "), flush=True)
        if verdict in ("BUG editor-died", "BUG daemon-died"):
            break
    print(tally, f"logs of the edits seen running: {ran['count']}", flush=True)
    if PLAY:
        probe("stop", r"^[0-9:.]+ stopped", timeout=60)


# Stopped from outside, the files edited go back as they were (`finally`).
signal.signal(signal.SIGTERM, lambda *_: sys.exit(1))
signal.signal(signal.SIGHUP, lambda *_: sys.exit(1))
main()
