"""Run in the pinned Lean project: lake env python3 /path/to/verify-reciprocal-bands.py.

Sources may be specified by module name on the command line. The default goal is
the simultaneous upper seventeen bounds. This builds their local dependencies in
a temporary directory. The pinned Mathlib build must already be available.
"""
import os
import re
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

def main():
    root = Path(__file__).resolve().parent
    modules = sys.argv[1:] or ["ReciprocalUpperBands"]
    prior = [str(Path(p).resolve()) for p in os.getenv("LEAN_PATH", "").split(os.pathsep) if p]
    seen = set()
    with TemporaryDirectory(prefix="lean-reciprocal-") as build:
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([build, *prior]))
        def compile_module(name):
            source = root / (name + ".lean")
            if name in seen:
                return
            imports = re.findall(r"^import ([\w.]+)\s*$", source.read_text(), re.MULTILINE)
            for parent in imports:
                if (root / (parent + ".lean")).is_file():
                    compile_module(parent)
            print("Checking", name, flush=True)
            run = subprocess.run(["lean", "-j1", "-o", str(Path(build, name+".olean")), source.name],
                                 cwd=root, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            print(run.stdout, end="")
            run.check_returncode()
            if "sorryAx" in run.stdout:
                raise RuntimeError(f"{name} depends on a placeholder")
            seen.add(name)
        for module in modules:
            compile_module(module)

if __name__ == "__main__":
    main()
