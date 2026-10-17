#!/usr/bin/env python3
"""Fail if an explicit theorem root uses an axiom outside Lean's standard three."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent

def check():
    result = subprocess.run(["lake", "env", "lean", "-j1", "-M3072", "Airbender/Checks/Axioms.lean"],
                            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise ValueError(result.stdout[-4000:])
    groups = re.findall(r"depends on axioms:\s*\[([^]]*)\]", result.stdout)
    used = {name.strip() for group in groups for name in group.split(",") if name.strip()}
    unexpected = used - {"propext", "Classical.choice", "Quot.sound"}
    if unexpected:
        raise ValueError("unexpected theorem axioms: " + ", ".join(sorted(unexpected)))
    roots = re.findall(r"^#print axioms (\S+)$", (ROOT / "Airbender/Checks/Axioms.lean").read_text(), re.M)
    count = len(groups) + result.stdout.count("does not depend on any axioms")
    if count != len(roots):
        raise ValueError(f"expected {len(roots)} audited roots, saw {count}")
    return count, sorted(used)

if __name__ == "__main__":
    try:
        count, used = check()
        print(f"PASS {count} axiom roots; only " + ", ".join(used))
    except ValueError as error:
        raise SystemExit(f"FAIL {error}") from error
