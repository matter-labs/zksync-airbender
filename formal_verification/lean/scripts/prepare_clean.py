#!/usr/bin/env python3
"""Apply hash-guarded compatibility fixes to the pinned Clean source."""

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
        (b"(circuit M).localLength input = 0 := by simp only [circuit_norm, circuit]",
         b"(circuit M).localLength input = 0 := by rfl"),
        (b"(circuit M (F:=F)).channelsWithGuarantees = [] := by simp only [circuit_norm, circuit]",
         b"(circuit M (F:=F)).channelsWithGuarantees = [] := by rfl"),
    ])

prepare("Types/U64.lean",
    "cecba15cf8d604fdcb3b97f408bf91c2bfafc11ea4a2f07ca788a28c28448f3b", [
        (b"    simp_all [circuit_norm, main, ByteTable, Normalized, explicit_provable_type]",
         b"    cases x_var\n    simp_all [circuit_norm, main, ByteTable, Normalized, explicit_provable_type]"),
    ])

# Keep the reference definitions and the lemma statement. Use transitivity
# directly; the new grw result has a non-strict final side condition.
prepare("Utils/Field.lean",
    "4a57afe112b29b8bf88fc686c7973aa8dd9f1956cbc4cd51457308ca4c0c1c0e", [
        (b"  grw [Nat.mod_lt x.val c.pos]\n  exact lt\n",
         b"  exact lt_trans (Nat.mod_lt x.val c.pos) lt\n"),
    ])

# Restore old elaborator transparency only for four dependent-vector proofs.
# The official kernel still checks their unchanged statements and proof terms.
prepare("Circuit/Provable.lean",
    "1d72d24c992c88172f6db2e2f8278480bea11bb080121ba487122e8bc0a8f8b7", [
        (marker, b"set_option backward.isDefEq.respectTransparency false in\n"
         b"set_option backward.isDefEq.respectTransparency.types false in\n" + marker)
        for marker in (
            b"theorem fromElements_toElements {F} : (cs : List WithProvableType)",
            b"theorem toElements_fromElements {F} : (cs : List WithProvableType)",
            b"/--\n`eval` === `ProvableStruct.eval`",
            b"omit [FiniteField F] in\n/--\n  `varFromOffset` === `ProvableStruct.varFromOffset`",
        )
    ] + [
        (b"    rw [componentsFromElements, componentsToElements,\n"
         b"      Vector.cast_take_append_of_eq_length, Vector.cast_drop_append_of_eq_length,",
         b"    change @ProvableTypeList.cons F c cs\n"
         b"      (fromElements (((toElements a ++ componentsToElements cs as).take (size c.type)).cast Nat.min_add_right_self))\n"
         b"      (componentsFromElements cs (((toElements a ++ componentsToElements cs as).drop (size c.type)).cast (Nat.add_sub_self_left _ _))) = .cons a as\n"
         b"    rw [Vector.cast_take_append_of_eq_length, Vector.cast_drop_append_of_eq_length,"),
    ])

# The same elaborator compatibility is local to the failing witness/channel proofs.
prepare("Circuit/WitnessIR.lean",
    "b7939360567385ef508c587e1794160a10d7e8fef71605ef9ad914b4c521dc58", [
        (b"theorem eval_eq_eval {M : TypeMap}",
         b"set_option backward.isDefEq.respectTransparency false in\n"
         b"set_option backward.isDefEq.respectTransparency.types false in\n"
         b"theorem eval_eq_eval {M : TypeMap}"),
    ])

prepare("Circuit/Channel.lean",
    "f14aae4a3f003584818b42e4e562077573a3c5a612b67e4835289bbeb814b9c4", [
        (marker, b"set_option backward.isDefEq.respectTransparency false in\n"
         b"set_option backward.isDefEq.respectTransparency.types false in\n" + marker)
        for marker in (
            b"lemma channelInteraction_toRaw_inj {",
            b"lemma eval_pulled {", b"lemma eval_pushed {",
            b"lemma eval_pulledIf {", b"lemma eval_pushedIf {",
        )
    ])

# Keep transparency compatibility local to the failing memory proofs.
prepare("Utils/OfflineMemory.lean",
    "f700223f02f81c7f0db78a076245870cd6886eb8ca04975c46c45767e0cb8d5c", [
        (marker, b"set_option backward.isDefEq.respectTransparency false in\n"
         b"set_option backward.isDefEq.respectTransparency.types false in\n" + marker)
        for marker in (
            b'example : MemoryAccessList.isConsistentOnline [\n',
            b'example : \xc2\xac MemoryAccessList.isConsistentOnline [\n',
            b'theorem MemoryAccessList.filterAddress_cons (head : MemoryAccess) (tail : MemoryAccessList) (addr : \xe2\x84\x95) :\n',
            b'/--\n  If a memory access list contains only accesses to a single address, then the following two consistency are equivalent:\n  - the online consistency check\n  - the single address consistency check\n-/\ntheorem MemoryAccessList.isConsistentSingleAddress_iff (accesses : MemoryAccessList) (addr : \xe2\x84\x95) (h_sorted : accesses.isTimestampSorted)\n',
            b'/--\n  The last write value for a specific address is the same whether we compute it on the full list\n  or on the filtered list on that address.\n-/\ntheorem MemoryAccessList.lastWriteValue_filter (accesses : MemoryAccessList)\n',
            b'/--\n  If a memory access list is online consistent, then the filtered list for a specific address is\n  online consistent as well.\n-/\ntheorem MemoryAccessList.isConsistentOnline_filter_of_consistentOnline (accesses : MemoryAccessList) (h_sorted : accesses.isTimestampSorted)\n',
            b'theorem MemoryAccessList.isTimestampSorted_cons (head : MemoryAccess) (tail : MemoryAccessList) :\n',
            b'theorem MemoryAccessList.isConsistentSingleAddress_filterAddress_of_cons (head : MemoryAccess) (tail : MemoryAccessList)\n',
            b'theorem MemoryAccessList.isConsistentSingleAddress_cons_forall (head : MemoryAccess) (tail : MemoryAccessList)\n',
            b'/--\n  A memory access list is consistent if and only if, for each possible address, considering\n  only the accesses to that address, the single address consistency check holds.\n-/\ntheorem MemoryAccessList.isConsistent_iff_all_single_address (accesses : MemoryAccessList) (h_sorted : accesses.isTimestampSorted) :\n',
            b'theorem MemoryAccessList.filterAddress_sorted_from_addressTimestampSorted\n',
            b'theorem MemoryAccessList.isConsistentSingleAddress_filterAddress_forall_of_cons\n',
            b'theorem MemoryAccessList.filterAddress_empty_when_address_changes\n',
            b'theorem MemoryAccessList.isConsistentOffline_implies_single_address\n',
            b'theorem MemoryAccessList.isConsistentOffline_iff_all_single_addresses (accesses : MemoryAccessList) (h_sorted : accesses.isAddressTimestampSorted) (h_nodup : accesses.Notimestampdup) :\n',
            b'/--\n  Technical lemma for soundness: if there exists two address-timestamp sorted lists of memory accesses\n  that are both permutations of the same timestamp-sorted list, then they must be equal.\n\n  Intuition: since the input list is timestamp strictly sorted, then there are no two timestamps in l1\n  that are equal, and therefore, for that class of lists, any address-timestamp sorted list is unique.\n  (This is true in general, if the initial list contains no duplicates, then any sorting is unique.)\n-/\nlemma MemoryAccessList.eq_of_perm_of_sorted {l1 l2 l3 : MemoryAccessList} (h_l1_sorted: l1.isTimestampSorted)\n',
            b'/--\n  This is the main theorem of this file.\n\n  A list of timestamp-sorted memory accesses is consistent if and only if there exists a permutation of the list\n  that is address-sorted, and such that the offline consistency check holds.\n-/\ntheorem MemoryAccessList.isConsistentOnline_iff_isConsistentOffline\n',
        )
    ])
