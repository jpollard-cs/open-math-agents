"""Rebuild in the pinned formal-conjectures checkout using its cached Mathlib.

From that checkout run:
    lake env python3 /path/to/verify-reciprocal-bands.py

The default checks all 48 bands, then composes the medium-prime result with
the project's small-prime proof. Pass module names to check a narrower result.
The manuscript directory includes the accepted parent reduction from PR 5169.
"""
import os
import re
import subprocess
import sys
from pathlib import Path
from tempfile import TemporaryDirectory


def main():
    source_root = Path(__file__).resolve().parent
    goals = sys.argv[1:] or ["ReciprocalCompleteFourNinths"]
    paths = [str(Path(p).resolve()) for p in os.getenv("LEAN_PATH", "").split(os.pathsep) if p]
    checked = set()
    with TemporaryDirectory(prefix="lean-reciprocal-") as build:
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([build, *paths]))

        def check(name):
            if name in checked:
                return
            relative = Path(*name.split(".")).with_suffix(".lean")
            source = source_root / relative
            for parent in re.findall(r"^import ([\w.]+)\s*$", source.read_text(), re.MULTILINE):
                local = source_root / Path(*parent.split(".")).with_suffix(".lean")
                if local.exists():
                    check(parent)
            output = (Path(build) / relative).with_suffix(".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            print("Checking", name, flush=True)
            run = subprocess.run(["lean", "-j1", "-o", str(output), str(relative)], cwd=source_root,
                                 env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            print(run.stdout, end="", flush=True)
            run.check_returncode()
            if "sorryAx" in run.stdout:
                raise RuntimeError(f"{name} depends on a placeholder")
            checked.add(name)
        for name in goals:
            check(name)


if __name__ == "__main__":
    main()
