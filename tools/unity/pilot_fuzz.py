#!/usr/bin/env python3
"""Edits the game's files as a person would, one at a time, through Pilot's
own hot reload (Unity → Hot Reload, `UnityHotReload.swift`) into the running
editor — and back.

Pilot has to be running on the project with hot reload on (for instance a
copy launched with `PILOT_HOT_RELOAD=1`). Each case picks a file of
Assembly-CSharp and an edit (`examples/mutate`), writes it to disk — Pilot
sees it through FSEvents as it would an edit from another editor — and reads
what Pilot made of it from `Temp/PilotProbe/hud.jsonl`:

- a file that does not compile is `broken`, and one that does is not;
- spacing changes nothing that runs (`same`), code that runs is a `patch`
  (or a `reload` when only a whole build carries it), and a patch applies;
- the editor's log says nothing only broken code makes the runtime say;
- the edit taken back comes back the same way.

One line per case; what failed is kept under `<work>/<seed>/`.

usage: pilot_fuzz.py <project> <mutate> <defines file> <work> [cases] [first seed]
"""
import json
import os
import random
import re
import subprocess
import sys
import time

PROJECT, MUTATE, DEFINES_FILE, WORK = sys.argv[1:5]
CASES = int(sys.argv[5]) if len(sys.argv) > 5 else 100
FIRST = int(sys.argv[6]) if len(sys.argv) > 6 else 1
DEFINES = open(DEFINES_FILE, encoding="utf-8").read().strip()
HUD = os.path.join(PROJECT, "Temp/PilotProbe/hud.jsonl")
EDITOR_LOG = os.path.expanduser("~/Library/Logs/Unity/Editor.log")
RUNTIME_BROKEN = re.compile(r"InvalidProgramException|MissingMethodException|MissingFieldException|TypeLoadException|"
                            r"BadImageFormatException|ExecutionEngineException|VerificationException|"
                            r"Native Crash|Received signal SIG|\* Assertion")
KINDS = [kind for kind in os.environ.get("PILOT_FUZZ_KINDS", "").split(",") if kind]
# The game in Play Mode while the patches go in, as one would test them.
PLAY = bool(os.environ.get("PILOT_FUZZ_PLAY"))
PROBE = os.path.join(PROJECT, "Temp/PilotProbe")
# Only files whose text matches, for edits most files have nothing for.
GREP = re.compile(os.environ["PILOT_FUZZ_GREP"]) if os.environ.get("PILOT_FUZZ_GREP") else None


def probe(command, pattern, timeout=120):
    log = os.path.join(PROBE, "log.txt")
    at = size(log)
    with open(os.path.join(PROBE, "cmd.txt"), "a") as file:
        file.write(command + "\n")
    end = time.time() + timeout
    while time.time() < end:
        with open(log, encoding="utf-8", errors="replace") as file:
            file.seek(at)
            for line in file.read().splitlines():
                if re.search(pattern, line):
                    return line
        time.sleep(0.1)
    return None


def size(path):
    return os.path.getsize(path) if os.path.exists(path) else 0


def sources():
    """Assembly-CSharp's own files, from the debug build's response file."""
    rsp = max((os.path.join(root, name) for root, _, names in os.walk(os.path.join(PROJECT, "Library/Bee/artifacts"))
               for name in names if name == "Assembly-CSharp.rsp" and "Dbg" in root), key=os.path.getmtime)
    found = []
    for line in open(rsp, encoding="utf-8"):
        line = line.strip().strip('"')
        if line.startswith("Assets/") and line.endswith(".cs") and os.path.exists(os.path.join(PROJECT, line)):
            found.append(line)
    if GREP:
        found = [path for path in found
                 if GREP.search(open(os.path.join(PROJECT, path), encoding="utf-8", errors="replace").read())]
    return found


def event_for(name, at, timeout):
    """The first event of the hot reload window after `at` about `name`,
    other than "Reloading…", which a reload's own event follows."""
    end = time.time() + timeout
    while time.time() < end:
        if size(HUD) > at:
            with open(HUD, encoding="utf-8", errors="replace") as file:
                file.seek(at)
                for line in file.read().splitlines():
                    try:
                        entry = json.loads(line)
                    except ValueError:
                        continue
                    if entry.get("file") == name and entry.get("title") != "Reloading…":
                        return entry
        time.sleep(0.05)
    return None


def write(path, text, bom):
    with open(path, "wb") as file:
        file.write((b"\xef\xbb\xbf" if bom else b"") + text.encode("utf-8"))


def verdict(expect, entry):
    """None when what Pilot did fits what the edit is, else why not."""
    if entry is None:
        return "no answer from Pilot"
    kind = entry["kind"]
    if kind == "failed":
        return f"failed: {entry.get('title')}: {entry.get('detail')}"
    if expect == "broken":
        return None if kind == "broken" else f"a broken file came to {kind}"
    if kind == "broken":
        return f"compiles, but Pilot said broken: {entry.get('detail')}"
    if expect == "spacing":
        return None if kind == "same" else f"spacing came to {kind}: {entry.get('title')}"
    if expect == "patch" and kind == "same":
        return "code that runs changed, but Pilot said nothing did"
    return None


def main():
    files = sources()
    os.makedirs(WORK, exist_ok=True)
    tally = {}
    print(f"{len(files)} files", flush=True)
    if PLAY:
        print(f"play: {probe('play', r'^[0-9:.]+ (playing|failed)')}", flush=True)
        time.sleep(8)
    for seed in range(FIRST, FIRST + CASES):
        chooser = random.Random(seed)
        relative = chooser.choice(files)
        path = os.path.join(PROJECT, relative)
        name = os.path.basename(relative)
        raw = open(path, "rb").read()
        bom = raw.startswith(b"\xef\xbb\xbf")
        original = raw.decode("utf-8-sig", errors="replace")
        arguments = [MUTATE, path, str(seed)]
        if KINDS:
            arguments.append(chooser.choice(KINDS))
        made = subprocess.run(arguments + ["--define", DEFINES], capture_output=True, text=True)
        if made.returncode != 0 or not made.stdout:
            continue
        # The mutated text, as `original`, without the mark `write` puts back.
        made.stdout = made.stdout.lstrip("\ufeff")
        kind, owner, member, expect = (made.stderr.strip().split("\t") + ["", "", "", ""])[:4]
        log_at = size(EDITOR_LOG)
        started = time.time()
        at = size(HUD)
        write(path, made.stdout, bom)
        entry = event_for(name, at, 300)
        took = time.time() - started
        wrong = verdict(expect, entry)
        # Taken back: whatever the edit did, the original text compiles.
        at = size(HUD)
        write(path, original, bom)
        back = event_for(name, at, 300)
        if wrong is None:
            if back is None:
                wrong = "taking it back: no answer from Pilot"
            elif back["kind"] in ("broken", "failed"):
                wrong = f"taking it back: {back['kind']}: {back.get('detail')}"
        time.sleep(0.5)
        with open(EDITOR_LOG, encoding="utf-8", errors="replace") as file:
            file.seek(log_at)
            said = RUNTIME_BROKEN.search(file.read())
        if wrong is None and said:
            wrong = f"the editor said {said.group(0)}"
        got = entry["kind"] if entry else "none"
        tally[got] = tally.get(got, 0) + 1
        mark = "ok  " if wrong is None else "FAIL"
        print(f"{mark} {seed:5} {kind:15} {expect:7} → {got:7} {took:5.1f} s  {relative}"
              + (f"\n      {wrong}" if wrong else ""), flush=True)
        if wrong:
            folder = os.path.join(WORK, str(seed))
            os.makedirs(folder, exist_ok=True)
            with open(os.path.join(folder, name), "w", encoding="utf-8") as file:
                file.write(made.stdout)
            with open(os.path.join(folder, "what.txt"), "w", encoding="utf-8") as file:
                file.write(f"{relative}\n{kind}\t{owner}\t{member}\t{expect}\n{wrong}\n{json.dumps(entry)}\n")
    print("done", tally, flush=True)


if __name__ == "__main__":
    main()
