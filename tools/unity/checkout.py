#!/usr/bin/env python3
"""A branch checked out under a running editor, and back: the files of
Assembly-CSharp an older commit had otherwise are written at once, sent as
one round, patched in or built whole and reloaded — then written back.

The repository is only read: each step goes `back` first-parent commits
from HEAD and takes the files of Assembly-CSharp that differ since — and
that the copy has as HEAD has them — as the older commit had them: changed,
deleted where it had none, written back where only it had one.

usage: checkout.py <repository> <steps> [back]
environment: RUSTLYN_SERVE_DIR, RUSTLYN_UNITY_PROJECT (the serve directory and the Unity project copy)
"""
import os
import signal
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


def git(repository, *arguments):
    return subprocess.run(["git", "-C", repository, *arguments], capture_output=True, check=False).stdout


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


def daemon(command, pattern=r"^(patch|nopatch|refused|unchanged|broken) ", timeout=600):
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
    return re.sub(r"^[0-9:.]+ ", "", line) if line else None


def take(round_files):
    """One round of the files; the editor patched or reloaded. What came of it."""
    started = time.time()
    answer = daemon("\t".join(round_files)) or "nopatch no answer"
    if answer.startswith("unchanged"):
        return f"unchanged {time.time() - started:.1f}s"
    if answer.startswith("broken"):
        return f"broken {answer[:200]}"
    if answer.startswith("patch "):
        applied = probe(f"hotpatch {answer.split()[-1]}", r"^[0-9:.]+ (hotpatched|failed hotpatch)", timeout=120)
        if applied and applied.startswith("hotpatched"):
            return f"patched {time.time() - started:.1f}s: {applied[:120]}"
        return f"FAILED patch: {applied}"
    built = daemon("rebuild", r"^(ready |refused the whole build)", timeout=300)
    if not built or not built.startswith("ready "):
        return f"FAILED whole build: {built}"
    log = os.path.join(PROBE, "log.txt")
    at = size(log)
    with open(os.path.join(PROBE, "cmd.txt"), "a") as file:
        file.write(f"reload {ASSEMBLY}\n")
    time.sleep(0.5)
    wake_editor(PROJECT)
    if not wait_line(log, at, r"^[0-9:.]+ (reloaded|failed)", timeout=600):
        return "FAILED the editor did not reload"
    probe(f"load {RUNTIME}", r"^[0-9:.]+ (loaded|failed)")
    verified = probe("verify", r"^[0-9:.]+ verify", timeout=600) or "verify: no answer"
    return f"reloaded {time.time() - started:.1f}s ({answer[:120]}) {verified[:140]}"


def main():
    repository, steps = sys.argv[1], int(sys.argv[2])
    back = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    with open(os.path.join(SERVE, "sources.txt"), encoding="utf-8") as file:
        sources = {line.strip() for line in file if line.strip().startswith("Assets/")}
    folders = {os.path.dirname(path) for path in sources}
    skipped = ("/Editor/", "/Plugins/", "/PilotProbe")

    def ours(path):
        return path in sources or (os.path.dirname(path) in folders and not any(part in path for part in skipped))

    commits = git(repository, "rev-list", "--first-parent", "HEAD", f"-n{steps * back + 1}").decode().split()
    for step in range(1, steps + 1):
        older = commits[step * back]
        listing = git(repository, "diff", "--no-renames", "--name-status", older, "HEAD", "--", "*.cs").decode().splitlines()
        # What the older commit had for each file of Assembly-CSharp that
        # differs: its text, or None where it had no such file.
        then = {}
        for line in listing:
            status, path = line.split("\t")[0], line.split("\t")[-1]
            if not ours(path):
                continue
            if os.path.exists(os.path.join(PROJECT, path)) and \
                    open(os.path.join(PROJECT, path), "rb").read() != git(repository, "show", f"HEAD:{path}"):
                continue  # the copy has its own edit of it
            then[path] = None if status == "A" else git(repository, "show", f"{older}:{path}")
        if not then:
            print(f"{step}: {older[:10]} skipped: nothing of Assembly-CSharp", flush=True)
            continue
        now = {path: (open(os.path.join(PROJECT, path), "rb").read()
                      if os.path.exists(os.path.join(PROJECT, path)) else None) for path in then}

        def write(state):
            for path, text in state.items():
                full = os.path.join(PROJECT, path)
                if text is None:
                    if os.path.exists(full):
                        os.remove(full)
                else:
                    os.makedirs(os.path.dirname(full), exist_ok=True)
                    with open(full, "wb") as file:
                        file.write(text)

        kinds = f"{sum(1 for t in then.values() if t is None)} gone, {sum(1 for p in then if now[p] is None)} back, " \
                f"{sum(1 for p, t in then.items() if t is not None and now[p] is not None)} changed"
        try:
            write(then)
            there = take(list(then))
        finally:
            write(now)
        # RUSTLYN_BACK_DLL: back onto that build instead of the daemon's
        # — csc's, to tell what of a crash is the reload's own.
        # RUSTLYN_REFRESH_FIRST: the editor imports what changed before it.
        if os.environ.get("RUSTLYN_REFRESH_FIRST"):
            print("refresh:", probe("refresh", r"^[0-9:.]+ (refreshed|failed)", timeout=600), flush=True)
        back_dll = os.environ.get("RUSTLYN_BACK_DLL")
        if back_dll:
            log = os.path.join(PROBE, "log.txt")
            at = size(log)
            with open(os.path.join(PROBE, "cmd.txt"), "a") as file:
                file.write(f"reload {back_dll}\n")
            time.sleep(0.5)
            wake_editor(PROJECT)
            again = wait_line(log, at, r"^[0-9:.]+ (reloaded|failed)", timeout=600) or "FAILED the editor did not reload"
        else:
            again = take(list(then))
        print(f"{step}: {older[:10]} {kinds} | there: {there} | back: {again}", flush=True)


# Stopped from outside, the files edited go back as they were (`finally`).
signal.signal(signal.SIGTERM, lambda *_: sys.exit(1))
signal.signal(signal.SIGHUP, lambda *_: sys.exit(1))
main()
