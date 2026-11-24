"""An editor in the background takes a reload it was asked for only once it
is brought to the front; the probe's other commands it takes as it is."""
import os
import subprocess


def wake_editor(project):
    """Brings the editor on `project` to the front, where RUSTLYN_WAKE_EDITOR
    allows taking the focus from whoever is typing."""
    if not os.environ.get("RUSTLYN_WAKE_EDITOR"):
        return False
    found = subprocess.run(["pgrep", "-f", f"Unity.app/Contents/MacOS/Unity .*-projectPath {project}"],
                           capture_output=True, text=True).stdout.split()
    for pid in found:
        subprocess.run(["osascript", "-e",
                        f'tell application "System Events" to set frontmost of (first process whose unix id is {pid}) to true'],
                       capture_output=True)
    return bool(found)
