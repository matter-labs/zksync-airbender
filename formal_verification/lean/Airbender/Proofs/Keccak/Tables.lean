import Airbender.Review.Circuits.Keccak.Tables.Setup

namespace Airbender.Keccak.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

private theorem byte_tag (tag index : Nat) : (byteRow tag index)[7] = tag := rfl
private theorem rotation_tag (key : Nat) : (rotationRow key)[7] = 40 := rfl

private theorem xor_rows {control : Fin 4096 → Vector Nat 6} (index : Fin 1249281)
    (selected : (setupRow control index)[7] = 4) :
    (setupRow control index)[0] < 256 ∧ (setupRow control index)[1] < 256 ∧
      (setupRow control index)[2] =
        (setupRow control index)[0] ^^^ (setupRow control index)[1] := by
  have size := index.isLt
  unfold setupRow at selected ⊢
  dsimp only at selected ⊢
  split_ifs at selected ⊢
  all_goals simp only [byte_tag, rotation_tag, Vector.getElem_replicate,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero] at selected
  all_goals norm_num at selected
  change (index.val - 1) / 256 < 256 ∧ (index.val - 1) % 256 < 256 ∧ _
  refine ⟨?_, Nat.mod_lt _ (by decide), rfl⟩
  omega

/-- The selected XOR region enforces byte bounds and exact XOR, through Clean's
    actual membership relation. No honest witness generator is assumed. -/
theorem xor_lookup {p : Nat} [Fact p.Prime] (hp : 256 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {entry : Vector (Expression (ZMod p)) 8}
    {env : Environment (ZMod p)}
    (h : (Lookup.mk (setupTable control).toRaw entry).Contains env)
    (selected : entry[7].eval env = 4) :
    (entry[0].eval env).val < 256 ∧ (entry[1].eval env).val < 256 ∧
    (entry[2].eval env).val < 256 ∧
      (entry[2].eval env).val = (entry[0].eval env).val ^^^ (entry[1].eval env).val := by
  have member := (Lookup.mk (setupTable control).toRaw entry).table.imply_soundness _ _ h
  change ∃ i : Fin 1249281, entry.map (Expression.eval env) =
    (setupRow control i).map (fun (n : Nat) => (n : ZMod p)) at member
  obtain ⟨i, row⟩ := member
  have column (j : Nat) (hj : j < 8) : entry[j].eval env = ((setupRow control i)[j] : ZMod p) := by
    have equation := congrArg (fun (v : Vector (ZMod p) 8) => v[j]) row
    simpa only [Vector.getElem_map] using equation
  have tagBound : (setupRow control i)[7] < p := by
    unfold setupRow
    dsimp only
    split_ifs <;> simp only [byte_tag, rotation_tag, Vector.getElem_replicate,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
      List.getElem_cons_zero] <;> omega
  have tagged : (setupRow control i)[7] = 4 := by
    have equation := congrArg ZMod.val ((column 7 (by decide)).symm.trans selected)
    rw [ZMod.val_natCast_of_lt tagBound] at equation
    have four : (4 : ZMod p).val = 4 := by
      simpa only [Nat.cast_ofNat] using ZMod.val_natCast_of_lt (n := p) (a := 4) (by omega)
    rw [four] at equation
    exact equation
  obtain ⟨a, b, xor⟩ := xor_rows i tagged
  have c : (setupRow control i)[2] < 256 := by
    rw [xor]
    exact Nat.xor_lt_two_pow (n := 8) a b
  have value (j : Nat) (hj : j < 8) (bound : (setupRow control i)[j] < 256) :
      (entry[j].eval env).val = (setupRow control i)[j] := by
    rw [column j hj]
    exact ZMod.val_natCast_of_lt (by omega)
  rw [value 0 (by decide) a, value 1 (by decide) b, value 2 (by decide) c]
  exact ⟨a, b, c, xor⟩
end Airbender.Keccak.Proofs
