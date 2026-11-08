#!/usr/bin/env python3
"""Point our Lean files at CleanCore (our transcription of Clean, human/CleanCore) instead of Clean.

Deterministic and idempotent; re-run after a rebase that brings files importing Clean.

  * `import Clean.X` -> `import CleanCore.X` whenever human/CleanCore/X.lean exists (an import of a Clean module
    we did not transcribe is reported and left alone, and the file then keeps needing Clean);
  * `_root_.N` -> `Airbender.N` for the transcribed names (CleanCore declares them in namespace `Airbender`, so
    bare references inside `namespace Airbender ...` already resolve to CleanCore; this includes the terms the
    importer, Human.Import.Exec.Emit, emits);
  * in a file outside `namespace Airbender` (and not opening it), bare `Expression.eval` -> `Airbender.Expression.eval`
    (macro quotations resolve names where the macro is defined, e.g. Slop.Eval's `eval_entry`), and Clean's
    root namespaces `Specs.BLAKE3`, `Specs.Keccak256`, `Utils.Bits`, `Utils.Rotation`, `ByteUtils`,
    `MemoryAccessList` and its root definitions `add32`, `not64`, `rotLeft64`, `rotRight64`, `rotRight32`
    -> `Airbender.` + the same (e.g. Human.ISA.Blake2s, Slop.Deleg.* in `namespace Spec`; not inside backticks);
  * `[FiniteField F]` -> `[Field F]` (CleanCore's semantics needs only a field; CleanCore.Equivalence, deviation 2);
  * test/Checks/Axioms.lean audits CleanCore's Keccak/BLAKE3 specs (`#print axioms Specs.X` ->
    `Airbender.Specs.X`) and keeps importing Clean for its audits of pinned Clean proofs.

Files left alone: CleanCore itself (incl. CleanCore.Equivalence, the one file meant to import Clean).

Usage: scripts/repoint_clean.py [--dry-run]   (from cs_formal_verification/lean)
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CORE = ROOT / "human" / "CleanCore"
ROOT_NAMES = ("FlatOperation", "Environment", "Expression", "Table", "RawTable", "Lookup", "StaticTable",
              "fields", "fieldPair", "fieldTriple", "field", "MemoryAccess")
KEEP_CLEAN_IMPORTS = {ROOT / "test/Checks/Axioms.lean"}


def rewrite(path: Path, text: str) -> tuple[str, list[str]]:
    notes = []

    def imp(m: re.Match) -> str:
        name = m.group(2)
        if path in KEEP_CLEAN_IMPORTS:
            return m.group(0)
        rel = Path(*name.split(".")[1:]).with_suffix(".lean")
        if (CORE / rel).is_file():
            return f"{m.group(1)}CleanCore.{'.'.join(name.split('.')[1:])}"
        notes.append(f"{path.relative_to(ROOT)}: no CleanCore transcription of {name}")
        return m.group(0)

    text = re.sub(r"^((?:public\s+|meta\s+)*import\s+)(Clean(?:\.[\w]+)+)", imp, text, flags=re.M)
    names = "|".join(ROOT_NAMES)
    text = re.sub(rf"\b_root_\.({names})\b", r"Airbender.\1", text)
    if not re.search(r"^\s*(?:namespace|open)\s+Airbender\b", text, re.M):
        text = re.sub(r"(?<![\w.])Expression\.eval\b", "Airbender.Expression.eval", text)
        text = re.sub(r"(?<![\w.`])(Specs\.(?:BLAKE3|Keccak256)|Utils\.(?:Bits|Rotation)|ByteUtils|MemoryAccessList)\b",
                      r"Airbender.\1", text)
        text = re.sub(r"(?<![\w.`'])(add32|not64|rotLeft64|rotRight64|rotRight32)\b(?!')", r"Airbender.\1", text)
    text = re.sub(r"\[FiniteField (\w+)\]", r"[Field \1]", text)
    if path.name == "Axioms.lean" and path.parent.name == "Checks":
        text = re.sub(r"^#print axioms Specs\.", "#print axioms Airbender.Specs.", text, flags=re.M)
    return text, notes


def main() -> int:
    dry = "--dry-run" in sys.argv[1:]
    changed, notes = [], []
    for src in ("human", "slop", "test"):
        for path in sorted((ROOT / src).rglob("*.lean")):
            if CORE in path.parents:
                continue
            text = path.read_text(encoding="utf-8")
            new, n = rewrite(path, text)
            notes += n
            if new != text:
                changed.append(path)
                if not dry:
                    path.write_text(new, encoding="utf-8")
    print(f"repointed {len(changed)} files to CleanCore")
    for path in changed:
        print(f"  {path.relative_to(ROOT)}")
    for note in notes:
        print(f"NOTE {note}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
