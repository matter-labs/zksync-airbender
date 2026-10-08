#!/usr/bin/env python3
"""Apply hash-guarded compatibility fixes to pinned Clean for Lean 4.31."""

from hashlib import sha256
from pathlib import Path
import subprocess


root = Path(__file__).resolve().parents[1]
clean = root / ".lake/packages/Clean/Clean"
if not (clean / "Utils/Bitwise.lean").exists():
    subprocess.run(["lake", "build", "Airbender.Import.Parse"], cwd=root, check=True)


def prepare(relative, expected_hash, replacements):
    """Accept only the pinned source or its known compatibility patches."""
    target = clean / relative
    source = target.read_bytes()
    original = source
    for old, new in reversed(replacements):
        original = original.replace(new, old)
    if sha256(original).hexdigest() != expected_hash:
        raise SystemExit(f"Clean {relative} differs from the pinned source; refusing to overwrite it")
    patched = original
    for old, new in replacements:
        if old not in patched:
            raise SystemExit(f"Clean {relative}: compatibility patch no longer matches")
        patched = patched.replace(old, new)
    if source != patched:
        target.write_bytes(patched)
        print(f"Clean: prepared {relative}; pinned source hash checked")
    else:
        print(f"Clean: {relative} already prepared; pinned source hash checked")


def factory(name):
    # Explicit proof arguments cannot be inferred by typeclass search. Preserve
    # constructor labels, reducibility, types and bodies as ordinary definitions.
    return (
        b"@[explicit_circuit_constructor]\ninstance " + name + b" ",
        b"@[explicit_circuit_constructor, implicit_reducible]\ndef " + name + b" ",
    )


prepare("Utils/Bitwise.lean",
    "78e8c4276003e13931f0743a4ac7b22782aede4a1fd1a96f4fb345e6df367c1a", [
        (b"import Mathlib.Analysis.Normed.Ring.Lemmas\n",
         b"import Std.Tactic.BVDecide\nimport Mathlib.Analysis.Normed.Ring.Lemmas\n"),
    ])

prepare("Circuit/Explicit.lean",
    "4321bdad0d94c524ca3aabe3e573b3db00c98b3cd2acfc79a2ff22fbfa69e70b",
    [factory(name) for name in (b"ExplicitCircuit.from_bind", b"ExplicitCircuit.from_map")])

# Proof reductions only: the definitions and theorem statements stay unchanged.
prepare("Circuit/Formal.lean",
    "2a6ad3267aae99480c5c12c5c2c36bf1a42558a20bfb934232b980d5edb424a0", [
        (b"simpa only [GeneralFormalCircuit.WithHint." + name + b",",
         b"simpa only [GeneralFormalCircuit.WithHint." + name + b",\n"
         b"      GeneralFormalCircuit." + name + b",")
        for name in (b"Soundness", b"Completeness")
    ])

prepare("Circuit/Theorems.lean",
    "e1c636074af2732755df74d22c432f67b0b2c0b2ec2e249d55024efed50a8219", [
        (b"simp only [bind_def, Functor.map, List.append_nil]",
         b"simp only [bind_def, Functor.map, pure_def, List.append_nil]"),
    ])

prepare("Circuit/Loops.lean",
    "d459d7102837e8d42331848ffd25d5fa81bca29adba3493d8ce5f33b63d80742", [
        (b"instance ConstantLength.fromConstantLength' ",
         b"@[implicit_reducible] def ConstantLength.fromConstantLength' "),
        (b"    convert this\n  rw", b"    convert this\n    rfl\n  rw"),
        *[factory(name) for name in
          (b"from_forEach", b"from_map_loop", b"from_mapFinRange", b"from_foldl", b"from_foldlRange")],
    ])

prepare("Gadgets/Equality.lean",
    "c7d8da75b1a8ea48da5c4ec151c33a84e7ae31a4e745ab6b5544b4d300e79a70", [
        (b"(config := {isSimp := false})", b"(isSimp := false)"),
        ("    · simp only [main, circuit_norm]".encode(),
         "    · cases input_var\n      simp only [main, circuit_norm]".encode()),
        (b"    simp only [Expression.eval] at h_holds\n    rw [neg_one_mul] at h_holds",
         b"    change Expression.eval env (.add ((toElements x_var)[i])\n"
         b"      (.mul (.const (-1)) ((toElements y_var)[i]))) = 0 at h_holds\n"
         b"    simp only [Expression.eval, neg_one_mul] at h_holds"),
        (b"    simp only [Vector.getElem_map, Vector.getElem_zip, Expression.eval, neg_one_mul]",
         b"    simp only [Vector.getElem_map, Vector.getElem_zip]\n"
         b"    change Expression.eval env.toEnvironment (.add ((toElements x_var)[i])\n"
         b"      (.mul (.const (-1)) ((toElements y_var)[i]))) = 0\n"
         b"    simp only [Expression.eval, neg_one_mul]"),
    ])

prepare("Types/U64.lean",
    "cecba15cf8d604fdcb3b97f408bf91c2bfafc11ea4a2f07ca788a28c28448f3b", [
        (b"    simp_all [circuit_norm, main, ByteTable, Normalized, explicit_provable_type]",
         b"    cases x_var\n    simp_all [circuit_norm, main, ByteTable, Normalized, explicit_provable_type]"),
    ])
