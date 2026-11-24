#!/usr/bin/env python3
"""How many of a project's real edits a hot patch would have taken.

Walks the project's recent commits that touch C#, and for each whose files
in the experimental copy are still as the commit left them, asks the daemon
(`classify`) whether going from the files as they were before the commit to
the files as it left them would have been a patch. A commit bundles many
saves, so a commit that needs a reload says only that one of its saves did:
the count is a floor.

The repository is only read. Assembly-CSharp's sources are the daemon's
source list; files of other assemblies are left out, and a commit that
touches none of Assembly-CSharp is not counted.

usage: replay.py <repository> <count of commits> [report.tsv]
environment: RUSTLYN_SERVE_DIR, RUSTLYN_UNITY_PROJECT (the serve directory and the Unity project copy)
"""
import os
import re
import subprocess
import sys
import time

SERVE = os.environ["RUSTLYN_SERVE_DIR"]
PROJECT = os.environ["RUSTLYN_UNITY_PROJECT"]
OUT = os.path.join(SERVE, "out.txt")
CMDS = os.path.join(SERVE, "cmds.txt")
WORK = os.path.join(SERVE, "replay")


def git(repository, *arguments):
    return subprocess.run(["git", "-C", repository, *arguments], capture_output=True, check=False).stdout


def wait_line(path, at, pattern, timeout=120):
    end = time.time() + timeout
    while time.time() < end:
        with open(path, encoding="utf-8", errors="replace") as file:
            file.seek(at)
            for line in file.read().splitlines():
                if re.search(pattern, line):
                    return line
        time.sleep(0.05)
    return None


def main():
    repository, count = sys.argv[1], int(sys.argv[2])
    report = sys.argv[3] if len(sys.argv) > 3 else os.path.join(WORK, "report.tsv")
    os.makedirs(WORK, exist_ok=True)
    with open(os.path.join(SERVE, "sources.txt"), encoding="utf-8") as file:
        sources = {line.strip() for line in file if line.strip().endswith(".cs")}
    commits = git(repository, "log", "--no-merges", "--format=%H%x09%s", f"-n{count}", "--", "*.cs")
    rows = []
    tally = {}
    for number, line in enumerate(commits.decode("utf-8", "replace").splitlines(), 1):
        commit, subject = line.split("\t", 1)
        changed = git(repository, "diff-tree", "--no-commit-id", "--name-status", "-r", "-M", commit, "--", "*.cs")
        # Files the commit left in Assembly-CSharp — the source list is the
        # project's as it is now, so it has those the commit added — each
        # with where its text was before: a renamed one under its old name.
        own = []
        for item in changed.decode("utf-8", "replace").splitlines():
            parts = item.split("\t")
            status, path = parts[0][0], parts[-1]
            if path in sources and status != "D":
                own.append((status, parts[1], path))
        if not own:
            verdict, why = "skip", "touches no file of Assembly-CSharp"
        else:
            drifted = [path for status, _, path in own
                       if open(os.path.join(PROJECT, path), "rb").read() != git(repository, "show", f"{commit}:{path}")
                       ] if all(os.path.exists(os.path.join(PROJECT, path)) for _, _, path in own) else ["missing"]
            if drifted:
                verdict, why = "skip", f"changed since: {drifted[0]}"
            else:
                manifest = os.path.join(WORK, f"{number}.txt")
                with open(manifest, "w", encoding="utf-8") as listing:
                    for index, (status, old, path) in enumerate(own):
                        if status == "A":
                            listing.write(f"{path}\t-\n")
                            continue
                        was = os.path.join(WORK, f"{number}-{index}.cs")
                        with open(was, "wb") as text:
                            text.write(git(repository, "show", f"{commit}^:{old}"))
                        listing.write(f"{path}\t{was}\n")
                at = os.path.getsize(OUT)
                with open(CMDS, "a") as commands:
                    commands.write(f"classify {manifest}\n")
                answer = wait_line(OUT, at, r"^classified ") or "classified nopatch no answer"
                verdict = answer.split()[1]
                why = answer.split(" ", 2)[2] if verdict == "nopatch" else ""
        tally[verdict] = tally.get(verdict, 0) + 1
        rows.append((commit[:10], verdict, why[:300], subject[:100]))
        print(f"{number:4} {commit[:10]} {verdict:8} {why[:150]}", flush=True)
    with open(report, "w", encoding="utf-8") as file:
        for row in rows:
            file.write("\t".join(row) + "\n")
    print(tally)


main()
