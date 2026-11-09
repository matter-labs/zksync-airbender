#!/usr/bin/env python3
"""Lake targets for the dependencies of verify.sh's build, so CI builds (and times) them apart from our code:

  - the Sail model library (SailRV32, with lean-sail);
  - the Clean modules our files import;
  - the C object (`:c.o`) of every dependency module the test executable links (`airbender_tests` links its whole
    import closure; Mathlib's cache ships `.olean` and `.c` files but no objects).

Run from cs_formal_verification/lean after `lake exe cache get`. Prints one target per line.
"""

import re
import sys
import tomllib
from pathlib import Path

ROOT = Path.cwd()
OURS = ("human", "slop", "test")
IMPORT = re.compile(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)", re.M)


def imports(src: Path) -> list[str]:
    """The imports in a file's header (before its first command; a docstring may mention `import`)."""
    text = re.sub(r"/-.*?-/", "", src.read_text(), flags=re.S)
    out = []
    for line in text.splitlines():
        t = line.strip()
        if not t or t.startswith("--") or t in ("module", "prelude"):
            continue
        m = IMPORT.match(line)
        if not m:
            break
        out.append(m.group(1))
    return out


def package_dirs() -> list[Path]:
    dirs = [ROOT / "sail-rv32", ROOT / "sail-rv32" / "lean-sail"]
    dirs += sorted(p for p in (ROOT / ".lake" / "packages").iterdir() if p.is_dir())
    return dirs


def find(mod: str, roots: list[Path]) -> Path | None:
    rel = Path(*mod.split(".")).with_suffix(".lean")
    for r in roots:
        if (r / rel).exists():
            return r / rel
    return None


def main() -> int:
    ours = [ROOT / d for d in OURS]
    deps = package_dirs()
    cfg = tomllib.loads((ROOT / "lakefile.toml").read_text())
    exe_root = cfg["lean_exe"][0]["root"]
    # the test executable's import closure, split into our modules and dependency modules
    seen: set[str] = set()
    dep_mods: set[str] = set()
    todo = [exe_root]
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        src = find(m, ours)
        if src is None:
            src = find(m, deps)
            if src is None:
                continue  # the toolchain's own modules (Init, Std, Lean, Lake): prebuilt
            dep_mods.add(m)
        todo += imports(src)
    # Clean modules imported anywhere in our sources (the spec's equivalence leaf imports Clean)
    clean = set()
    for d in ours:
        for p in d.rglob("*.lean"):
            clean.update(i for i in imports(p) if i == "Clean" or i.startswith("Clean."))
    print("SailRV32")
    for m in sorted(clean):
        print(m)
    for m in sorted(dep_mods):
        print(f"{m}:c.o")
    print(f"dependencies: SailRV32, {len(clean)} Clean imports, {len(dep_mods)} objects", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
