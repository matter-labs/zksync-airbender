#!/usr/bin/env python3
"""Apply one checked import fix to pinned Clean for Lean 4.31's bv_decide."""

from hashlib import sha256
from pathlib import Path
import subprocess


root = Path(__file__).resolve().parents[1]
target = root / ".lake/packages/Clean/Clean/Utils/Bitwise.lean"
if not target.exists():
    # Bootstrap the pinned dependencies without building the affected spec module.
    subprocess.run(["lake", "build", "Airbender.Import.Parse"], cwd=root, check=True)

original_hash = "78e8c4276003e13931f0743a4ac7b22782aede4a1fd1a96f4fb345e6df367c1a"
extra_import = b"import Std.Tactic.BVDecide\n"
source = target.read_bytes()
original = source[len(extra_import):] if source.startswith(extra_import) else source
if sha256(original).hexdigest() != original_hash:
    raise SystemExit("Clean Bitwise differs from the pinned source; refusing to overwrite it")

if source == original:
    target.write_bytes(extra_import + original)
    print("Clean: added BVDecide import; all upstream definitions and proofs unchanged")
else:
    print("Clean: BVDecide import already present; pinned source hash checked")
