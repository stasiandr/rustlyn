#!/usr/bin/env python3
"""Edit a running Unity editor's code by saving files.

Starts the daemon (`$RUSTLYN_SERVE_DIR/restart.sh`), waits for the editor on
the project to come up with the probe in it, loads the daemon's build into
it, and then watches the project's C#: each file saved goes to the daemon,
and the patch it answers with goes into the editor. An edit no patch can
carry is built whole and the editor reloaded on it. One line per save:

    ✓ HotTarget.cs  1.38 s  patched 2: HotTarget::Describe, ...
    ⟳ Shop.cs  reload: an interface was added ... 31.2 s

usage: hot.py
environment: RUSTLYN_SERVE_DIR, RUSTLYN_UNITY_PROJECT (the serve directory and the Unity project copy)
"""
import difflib
import json
import os
import threading
import re
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from wake import wake_editor  # noqa: E402

SERVE = os.environ["RUSTLYN_SERVE_DIR"]
PROJECT = os.environ["RUSTLYN_UNITY_PROJECT"]
PROBE = os.path.join(PROJECT, "Temp/PilotProbe")
OUT = os.path.join(SERVE, "out.txt")
CMDS = os.path.join(SERVE, "cmds.txt")
ASSEMBLY = os.path.join(SERVE, "Assembly-CSharp.dll")
RUNTIME = os.path.join(SERVE, "runtime/PilotRuntime.dll")
UNITY = os.environ.get("RUSTLYN_UNITY",
                       "/Applications/Unity/Hub/Editor/2022.3.76f1/Unity.app/Contents/MacOS/Unity")
# What is not the game's code, or is the probe that applies patches.
SKIPPED = ("/PilotProbe/", "/Editor/", "/Plugins/")


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


# Each watched file's text as it was last seen, for what a save changed in it.
TEXTS = {}


def remember(paths):
    for path in paths:
        try:
            with open(path, encoding="utf-8-sig", errors="replace") as file:
                TEXTS[path] = file.read()
        except OSError:
            TEXTS.pop(path, None)


def changed_lines(path, limit=16):
    """The lines a save changed in `path`, `+` and `-` before them, with the
    indentation they share taken off — and the file's text remembered."""
    was = TEXTS.get(path)
    remember([path])
    now = TEXTS.get(path)
    if was is None or now is None:
        return []
    lines = []
    for line in difflib.unified_diff(was.splitlines(), now.splitlines(), n=1, lineterm=""):
        if line.startswith(("---", "+++")):
            continue
        lines.append("⋯" if line.startswith("@@") else line.rstrip())
    if lines and lines[0] == "⋯":
        lines = lines[1:]
    bodies = [line[1:] for line in lines if line[:1] in "+- " and line[1:].strip()]
    indent = min((len(body) - len(body.lstrip()) for body in bodies), default=0)
    lines = [line if line == "⋯" else line[:1] + line[1 + indent:] for line in lines]
    return lines[:limit] + (["⋯"] if len(lines) > limit else [])


def event(kind, file="", title="", detail="", seconds=0.0, diff=None):
    """One event for the editor's Pilot Hot Reload window (PilotHud.cs)."""
    entry = {"time": time.strftime("%H:%M:%S"), "kind": kind, "file": file, "title": title,
             "detail": detail, "seconds": round(seconds, 2), "diff": diff or []}
    try:
        os.makedirs(PROBE, exist_ok=True)
        with open(os.path.join(PROBE, "hud.jsonl"), "a", encoding="utf-8") as stream:
            stream.write(json.dumps(entry, ensure_ascii=False) + "\n")
    except OSError:
        pass


def note(text):
    """The line shown in the editor too (PilotHud.cs): over its Scene and
    Game views, and in Window > Pilot Hot Reload. Nothing waits for it."""
    try:
        with open(os.path.join(PROBE, "cmd.txt"), "a") as file:
            file.write("note " + text.replace("\n", " ") + "\n")
    except OSError:
        pass


def short_members(applied):
    """`dev.A.B::M, dev.A.C::get_P` as `B.M, C.P`."""
    names = []
    for item in applied.split(", "):
        owner, _, member = item.strip().partition("::")
        member = member[4:] if member.startswith(("get_", "set_")) else member
        member = {".ctor": "constructor", ".cctor": "static constructor"}.get(member, member)
        names.append(f"{owner.split('.')[-1]}.{member}" if member else owner)
    return names


# Every method the patches since the editor's last reload replaced: a patch
# holds them all, and what a save changed is what is new among them.
PATCHED = set()


KEYWORDS = {"if", "for", "foreach", "while", "switch", "catch", "using", "return", "new", "lock", "fixed",
            "nameof", "typeof", "sizeof", "default", "base", "this", "await", "throw", "else", "get", "set"}


def declarations(diff):
    """What the save added or removed of the file's declarations, by its
    lines: `Added field OldRewards`, `Removed class SomeClass<T>`."""
    found = []
    for line in diff:
        sign, text = line[:1], line[1:].strip()
        if sign not in "+-" or not text or text.startswith(("//", "[")):
            continue
        verb = "Added" if sign == "+" else "Removed"
        kind_name = re.search(r"\b(class|struct|interface|enum|record)\s+(\w+(?:<[^>]*>)?)", text)
        if kind_name:
            found.append(f"{verb} {kind_name.group(1)} {kind_name.group(2)}")
            continue
        method = re.match(r"(?:(?:public|private|protected|internal|static|virtual|override|async|abstract|sealed|"
                          r"partial|unsafe|extern|new)\s+)*[\w<>\[\],.?]+\s+(\w+)\s*(?:<[^>]*>)?\s*\([^;]*$", text)
        if method and method.group(1) not in KEYWORDS and not text.startswith(("return", "var ", "await")):
            found.append(f"{verb} method {method.group(1)}")
            continue
        member = re.match(r"(?:public|private|protected|internal|static|readonly|const|volatile)\b[^(=]*?\b(\w+)\s*(=|;|\{|=>)", text)
        if member and member.group(1) not in KEYWORDS:
            what = "property" if member.group(2) in ("{", "=>") else "field"
            found.append(f"{verb} {what} {member.group(1)}")
    return list(dict.fromkeys(found))


def changed_by(name, applied, diff):
    """What the save changed, in a few words: the declarations it added or
    removed, or else the methods the patch has new — or, edited again, the
    file's own — or else just the file."""
    _, _, listed = applied.partition(": ")
    members = short_members(listed) if listed else []
    new = [member for member in members if member not in PATCHED]
    PATCHED.update(members)
    stem = os.path.splitext(name)[0]
    shown = declarations(diff) or new or [member for member in members if member.split(".")[0] == stem]
    if not shown:
        return f"Edited {stem}"
    more = f" and {len(shown) - 3} more" if len(shown) > 3 else ""
    return ", ".join(shown[:3]) + more


def say(text):
    print(f"{time.strftime('%H:%M:%S')} {text}", flush=True)


def probe(command, pattern, timeout=60):
    log = os.path.join(PROBE, "log.txt")
    at = size(log)
    with open(os.path.join(PROBE, "cmd.txt"), "a") as file:
        file.write(command + "\n")
    line = wait_line(log, at, pattern, timeout)
    return re.sub(r"^[0-9:.]+ ", "", line) if line else None


def load_build(reason):
    """The editor reloaded on the daemon's build, and the runtime loaded."""
    started = time.time()
    log = os.path.join(PROBE, "log.txt")
    at = size(log)
    with open(os.path.join(PROBE, "cmd.txt"), "a") as file:
        file.write(f"reload {ASSEMBLY}\n")
    if not wake_editor(PROJECT):
        say("⟳ switch to Unity: it reloads once it is in front")
    if not wait_line(log, at, r"^[0-9:.]+ (reloaded|failed)", timeout=1800):
        say("✗ the editor did not reload")
        return
    probe(f"load {RUNTIME}", r"^[0-9:.]+ (loaded|failed)")
    say(f"⟳ {reason}: the editor runs the daemon's build ({time.time() - started:.1f} s)")
    PATCHED.clear()
    event("reload", title="Reloaded on the new build", detail=reason, seconds=time.time() - started)


def members():
    """The daemon's sources, and the folders they are in: a file of another
    assembly is not Assembly-CSharp's to patch, and a new one belongs where
    the files beside it do."""
    with open(os.path.join(SERVE, "sources.txt"), encoding="utf-8") as file:
        listed = {os.path.join(PROJECT, line.strip()) for line in file if line.strip().startswith("Assets/")}
    return listed, {os.path.dirname(path) for path in listed}


MEMBERS, FOLDERS = set(), set()


def stamp(path):
    try:
        info = os.stat(path)
        return (info.st_mtime_ns, info.st_size)
    except FileNotFoundError:
        return None


def watched(path):
    """Whether a C# file is one the daemon builds: listed, or new beside them."""
    return (path.endswith(".cs") and not any(part in path for part in SKIPPED)
            and (path in MEMBERS or os.path.dirname(path) in FOLDERS))


FSEVENTS_SOURCE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fsevents.swift")


def file_events():
    """A queue of the C# paths macOS reports changed under Assets, from
    fsevents.swift built beside the daemon; None where it cannot be had,
    and the project is walked instead."""
    import queue
    built = os.path.join(SERVE, "fsevents")
    if not os.path.exists(built) or os.path.getmtime(built) < os.path.getmtime(FSEVENTS_SOURCE):
        made = subprocess.run(["swiftc", "-O", "-o", built, FSEVENTS_SOURCE], capture_output=True)
        if made.returncode != 0:
            say("file events are not to be had; walking the project instead")
            return None
    process = subprocess.Popen([built, os.path.realpath(os.path.join(PROJECT, "Assets"))],
                               stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    paths = queue.Queue()
    real = os.path.realpath(PROJECT)

    def pump():
        for line in process.stdout:
            path = line.strip()
            # Said of the real path; the watcher knows the project's own.
            if path.startswith(real):
                path = PROJECT + path[len(real):]
            paths.put(path)
    threading.Thread(target=pump, daemon=True).start()
    return paths


def told_paths(told):
    """The paths reported since the last look: waits for the first, then
    takes whatever came with it."""
    import queue
    try:
        found = {told.get(timeout=0.5)}
    except queue.Empty:
        return set()
    time.sleep(0.01)
    while True:
        try:
            found.add(told.get_nowait())
        except queue.Empty:
            return found


def sources():
    found = {}
    for root, directories, names in os.walk(os.path.join(PROJECT, "Assets")):
        for name in names:
            if name.endswith(".cs"):
                path = os.path.join(root, name)
                if not any(part in path for part in SKIPPED) and (path in MEMBERS or root in FOLDERS):
                    try:
                        found[path] = os.stat(path).st_mtime_ns
                    except FileNotFoundError:
                        pass
    return found


def editor_running():
    return bool(subprocess.run(["pgrep", "-f", f"Unity.app/Contents/MacOS/Unity .*-projectPath {PROJECT}"],
                               capture_output=True).stdout)


def stage():
    """The daemon's build where an editor about to start loads it from.

    The editor compiles at its start what changed since it last did: so it
    compiles first, without a window, and finds nothing to do when it opens
    — on this build rather than csc's, which saves it a reload."""
    say("the editor compiles what changed since it last ran (a minute or two)")
    subprocess.run([UNITY, "-batchmode", "-quit", "-projectPath", PROJECT,
                    "-logFile", os.path.join(SERVE, "batch-compile.log")],
                   stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    for cached in ["Library/ScriptAssemblies/Assembly-CSharp.dll",
                   "Library/Bee/artifacts/900b0aEDbg.dag/post-processed/Assembly-CSharp.dll"]:
        target = os.path.join(PROJECT, cached)
        if os.path.exists(target):
            with open(ASSEMBLY, "rb") as source, open(target + ".pilot", "wb") as staged:
                staged.write(source.read())
            os.replace(target + ".pilot", target)
            symbols = os.path.splitext(target)[0] + ".pdb"
            if os.path.exists(symbols):
                os.remove(symbols)
    say("the daemon's build is where the editor will load it from: open the project now")


def already_loaded():
    """Whether the editor started on the daemon's build as it is now — the
    one staged for it — so that loading it again is a reload for nothing."""
    started = wait_line(os.path.join(PROBE, "log.txt"), 0, r"started assembly", timeout=1) or ""
    loaded = os.path.join(PROJECT, "Library/ScriptAssemblies/Assembly-CSharp.dll")
    if "started assembly" not in started or not os.path.exists(loaded):
        return False
    with open(loaded, "rb") as first, open(ASSEMBLY, "rb") as second:
        return first.read() == second.read()


def wait_for_editor():
    """Until an editor on the project has started and loaded its scripts."""
    log = os.path.join(PROBE, "log.txt")
    while not wait_line(log, 0, r"started assembly|reloaded ", timeout=1):
        time.sleep(1)


def main():
    # What an editor that has quit left in the log says nothing of the one to
    # come.
    running = subprocess.run(["pgrep", "-f", f"Unity.app/Contents/MacOS/Unity .*-projectPath {PROJECT}"], capture_output=True).stdout
    if not running and os.path.exists(os.path.join(PROBE, "log.txt")):
        os.remove(os.path.join(PROBE, "log.txt"))
    say("starting the daemon (the first build takes about 30 s)")
    at = size(OUT)
    subprocess.run(["sh", os.path.join(SERVE, "restart.sh")], stdin=subprocess.DEVNULL,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
    if not wait_line(OUT, at, r"^generators ready", timeout=240):
        sys.exit("the daemon did not start")
    if not running:
        stage()
    say("the daemon is ready; waiting for the editor on the project")
    wait_for_editor()
    if already_loaded():
        probe(f"load {RUNTIME}", r"^[0-9:.]+ (loaded|failed)")
        say("the editor started on the daemon's build")
    else:
        load_build("start")
    global MEMBERS, FOLDERS
    MEMBERS, FOLDERS = members()
    known = sources()
    say(f"watching {len(known)} files — save one")
    event("info", title=f"watching {len(known)} files")
    threading.Thread(target=remember, args=(list(known),), daemon=True).start()
    told = file_events()
    while True:
        if told is None:
            time.sleep(0.05)
            now = sources()
        else:
            # What macOS says changed, rather than a walk of the project.
            touched = told_paths(told)
            now = dict(known)
            for path in touched:
                if watched(path):
                    try:
                        now[path] = os.stat(path).st_mtime_ns
                    except FileNotFoundError:
                        now.pop(path, None)
        changed = [path for path, stamp in now.items() if known.get(path) != stamp]
        # A file deleted is a change too: what it declared goes.
        changed += [path for path in known if path not in now]
        # An editor that writes a file in place may be caught halfway: the
        # file is read once it has stayed as it is for a moment.
        if changed:
            settled = {}
            while settled != {path: stamp(path) for path in changed}:
                settled = {path: stamp(path) for path in changed}
                time.sleep(0.03)
            for path in changed:
                try:
                    now[path] = os.stat(path).st_mtime_ns
                except FileNotFoundError:
                    now.pop(path, None)
        known = now
        if not changed:
            continue
        # Files saved together — a branch checked out, a refactoring —
        # are one round.
        started = time.time()
        relative = "\t".join(os.path.relpath(path, PROJECT) for path in changed)
        # What the save changed, shown in the editor: the first file's lines.
        diff = changed_lines(changed[0])
        remember(changed[1:])
        name = os.path.basename(changed[0]) if len(changed) == 1 else f"{len(changed)} files"
        at = size(OUT)
        with open(CMDS, "a") as file:
            file.write(relative + "\n")
        answer = wait_line(OUT, at, r"^(patch|nopatch|refused|unchanged|broken) ",
                           timeout=60 + 2 * len(changed)) or "nopatch no answer"
        if answer.startswith("unchanged"):
            say(f"· {name}  nothing the running code sees changed")
            event("same", name, "Nothing that runs changed", "spacing or comments", time.time() - started, diff)
            continue
        # Saved halfway through typing: nothing of it is built, and the
        # next save is read again.
        if answer.startswith("broken "):
            say(f"✗ {name}  does not compile, waiting for the next save: {answer[len('broken '):][:200]}")
            error = answer[len("broken "):].split(": error ", 1)[-1]
            event("broken", name, "Does not compile yet", error[:240], time.time() - started, diff)
            continue
        if answer.startswith("patch "):
            applied = probe(f"hotpatch {answer.split()[-1]}", r"^[0-9:.]+ (hotpatched|failed hotpatch)")
            took = time.time() - started
            if applied and applied.startswith("hotpatched"):
                say(f"✓ {name}  {took:.2f} s  {applied[len('hotpatched '):][:140]}")
                event("patch", name, changed_by(name, applied, diff), "patched into the running editor — no reload", took, diff)
            else:
                say(f"✗ {name}  the patch did not apply: {(applied or 'no answer')[:200]}")
                event("failed", name, "The patch did not apply", (applied or "no answer")[:240], took, diff)
            continue
        why = answer.split(" ", 1)[1] if " " in answer else answer
        # A file deleted under a running editor: a reload in place leaves
        # its objects of the deleted types to a backup the next reload
        # cannot read back ("MemoryStream is corrupted" — csc's build as
        # much as this one's). The editor starts again instead.
        if "was deleted" in answer:
            at = size(OUT)
            with open(CMDS, "a") as file:
                file.write("rebuild\n")
            wait_line(OUT, at, r"^(ready |refused the whole build)", timeout=240)
            say(f"⟳ {name}  a file was deleted: save the scenes and quit Unity — it starts again on the new build")
            event("deleted", name, "A file was deleted: quit Unity",
                  "save the scenes and quit; it starts again on the new build", diff=diff)
            while editor_running():
                time.sleep(1)
            log = os.path.join(PROBE, "log.txt")
            if os.path.exists(log):
                os.remove(log)
            stage()
            wait_for_editor()
            load_build("start again")
            continue
        say(f"⟳ {name}  needs a reload: {why[:200]}")
        reason = why.split(": ", 1)[-1] if ": " in why else why
        event("reload", name, "Reloading…", reason[:240], diff=diff)
        at = size(OUT)
        with open(CMDS, "a") as file:
            file.write("rebuild\n")
        built = wait_line(OUT, at, r"^(ready |refused the whole build)", timeout=240)
        if built and built.startswith("ready "):
            load_build(f"{name} ({time.time() - started:.1f} s with the build)")
        elif built:
            say(f"✗ {built[:240]}")
        else:
            say("✗ the whole build did not finish")

main()
