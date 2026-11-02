import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Blake2G.ImportedXor
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2G.Proofs

private theorem xor_row_bounds (width tag offset : Nat)
    (bound : offset < 2 ^ width * 2 ^ width) :
    (xorRow width tag offset)[0] < 2 ^ width ∧
    (xorRow width tag offset)[1] < 2 ^ width ∧
    (xorRow width tag offset)[2] =
      (xorRow width tag offset)[0] ^^^ (xorRow width tag offset)[1] := by
  have positive : 0 < 2 ^ width := Nat.pow_pos (by decide)
  change offset / 2 ^ width < 2 ^ width ∧ offset % 2 ^ width < 2 ^ width ∧ _ = _
  exact ⟨(Nat.div_lt_iff_lt_mul positive).2 bound, Nat.mod_lt _ positive, rfl⟩

private theorem xor_tags_injective :
    Function.Injective (fun k : Fin 5 => (#v[4, 17, 18, 19, 20][k] : Nat)) := by
  decide +kernel

private theorem selected_xor_row (region kind : Fin 5) (offset : Nat)
    (bound : offset < 2 ^ (#v[8, 3, 4, 7, 9][region]) * 2 ^ (#v[8, 3, 4, 7, 9][region]))
    (selected : (xorRow (#v[8, 3, 4, 7, 9][region]) (#v[4, 17, 18, 19, 20][region]) offset)[8] =
      (#v[4, 17, 18, 19, 20][kind])) :
    (xorRow (#v[8, 3, 4, 7, 9][region]) (#v[4, 17, 18, 19, 20][region]) offset)[0] <
      2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (xorRow (#v[8, 3, 4, 7, 9][region]) (#v[4, 17, 18, 19, 20][region]) offset)[1] <
      2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (xorRow (#v[8, 3, 4, 7, 9][region]) (#v[4, 17, 18, 19, 20][region]) offset)[2] =
      (xorRow (#v[8, 3, 4, 7, 9][region]) (#v[4, 17, 18, 19, 20][region]) offset)[0] ^^^
      (xorRow (#v[8, 3, 4, 7, 9][region]) (#v[4, 17, 18, 19, 20][region]) offset)[1] := by
  have tags : (#v[4, 17, 18, 19, 20][region] : Nat) = (#v[4, 17, 18, 19, 20][kind]) := selected
  have same := xor_tags_injective tags
  subst kind
  exact xor_row_bounds _ _ _ bound

private theorem xor_rows {control : Fin 512 → Vector Nat 7} (index : Fin 344896)
    (kind : Fin 5) (selected : (referenceSetupRow control index)[8] = (#v[4, 17, 18, 19, 20][kind])) :
    (referenceSetupRow control index)[0] < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (referenceSetupRow control index)[1] < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (referenceSetupRow control index)[2] =
      (referenceSetupRow control index)[0] ^^^ (referenceSetupRow control index)[1] := by
  have size := index.isLt
  unfold referenceSetupRow at selected ⊢
  dsimp only at selected ⊢
  split_ifs at selected ⊢
  · exact selected_xor_row 0 kind index.val (by norm_num; omega) selected
  · exact selected_xor_row 1 kind (index.val - 65536) (by norm_num; omega) selected
  · exact selected_xor_row 2 kind (index.val - 65600) (by norm_num; omega) selected
  · exact selected_xor_row 3 kind (index.val - 65856) (by norm_num; omega) selected
  · exact selected_xor_row 4 kind (index.val - 82240) (by norm_num; omega) selected
  · fin_cases kind <;> norm_num at selected

/-- Each selected XOR region in the native static table enforces its chunk bounds
    and exact XOR. This uses table membership, not an assumed circuit result. -/
theorem xor_lookup {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    {control : Fin 512 → Vector Nat 7} {entry : Vector (Expression (ZMod p)) 9}
    {env : Environment (ZMod p)} (kind : Fin 5)
    (h : (Lookup.mk (setupTable control).toRaw entry).Contains env)
    (selected : entry[8].eval env = ((#v[4, 17, 18, 19, 20][kind] : Nat) : ZMod p)) :
    (entry[0].eval env).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (entry[1].eval env).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (entry[2].eval env).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (entry[2].eval env).val = (entry[0].eval env).val ^^^ (entry[1].eval env).val := by
  have member := (Lookup.mk (setupTable control).toRaw entry).table.imply_soundness _ _ h
  change ∃ i : Fin 344896, entry.map (Expression.eval env) =
    (setupRow control i).map (fun (n : Nat) => (n : ZMod p)) at member
  simp only [setup_row_characterization] at member
  obtain ⟨i, row⟩ := member
  have column (j : Nat) (hj : j < 9) :
      entry[j].eval env = ((referenceSetupRow control i)[j] : ZMod p) := by
    have equation := congrArg (fun (v : Vector (ZMod p) 9) => v[j]) row
    simpa only [Vector.getElem_map] using equation
  have tagBound : (referenceSetupRow control i)[8] < p := by
    unfold referenceSetupRow
    dsimp only
    split_ifs <;> simp [xorRow] <;> omega
  have wantedBound : (#v[4, 17, 18, 19, 20][kind] : Nat) < p := by
    fin_cases kind <;> dsimp <;> omega
  have tagged : (referenceSetupRow control i)[8] = (#v[4, 17, 18, 19, 20][kind]) := by
    have equation := congrArg ZMod.val ((column 8 (by decide)).symm.trans selected)
    simp only [ZMod.val_natCast] at equation
    rw [Nat.mod_eq_of_lt tagBound, Nat.mod_eq_of_lt wantedBound] at equation
    exact equation
  obtain ⟨a, b, xor⟩ := xor_rows i kind tagged
  have c : (referenceSetupRow control i)[2] < 2 ^ (#v[8, 3, 4, 7, 9][kind]) := by
    rw [xor]
    exact Nat.xor_lt_two_pow a b
  have widthBound : 2 ^ (#v[8, 3, 4, 7, 9][kind]) ≤ 512 := by fin_cases kind <;> norm_num
  have value (j : Nat) (hj : j < 9) (bound : (referenceSetupRow control i)[j] < 2 ^ (#v[8, 3, 4, 7, 9][kind])) :
      (entry[j].eval env).val = (referenceSetupRow control i)[j] := by
    rw [column j hj]
    exact ZMod.val_natCast_of_lt (by omega)
  rw [value 0 (by decide) a, value 1 (by decide) b, value 2 (by decide) c]
  exact ⟨a, b, c, xor⟩

set_option maxRecDepth 4096 in
/-- Tag 28 selects the controller region and binds every output column to one
    supplied row. No assumptions about that row's behavior are used here. -/
theorem control_lookup {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    {control : Fin 512 → Vector Nat 7} {entry : Vector (Expression (ZMod p)) 9}
    {env : Environment (ZMod p)}
    (h : (Lookup.mk (setupTable control).toRaw entry).Contains env)
    (selected : entry[8].eval env = 28) :
    ∃ key : Fin 512, entry[0].eval env = (key.val : ZMod p) ∧
      ∀ j : Fin 7, entry[j.val + 1].eval env = ((control key)[j] : ZMod p) := by
  have member := (Lookup.mk (setupTable control).toRaw entry).table.imply_soundness _ _ h
  change ∃ i : Fin 344896, entry.map (Expression.eval env) =
    (setupRow control i).map (fun (n : Nat) => (n : ZMod p)) at member
  simp only [setup_row_characterization] at member
  obtain ⟨i, row⟩ := member
  have column (j : Nat) (hj : j < 9) :
      entry[j].eval env = ((referenceSetupRow control i)[j] : ZMod p) := by
    have equation := congrArg (fun (v : Vector (ZMod p) 9) => v[j]) row
    simpa only [Vector.getElem_map] using equation
  have tagBound : (referenceSetupRow control i)[8] < p := by
    unfold referenceSetupRow
    dsimp only
    split_ifs <;> simp [xorRow] <;> omega
  have tagged : (referenceSetupRow control i)[8] = 28 := by
    have equation := congrArg ZMod.val ((column 8 (by decide)).symm.trans selected)
    have literal : (28 : ZMod p).val = 28 := by
      change ((28 : Nat) : ZMod p).val = 28
      exact ZMod.val_natCast_of_lt (by omega)
    rw [ZMod.val_natCast_of_lt tagBound, literal] at equation
    exact equation
  have region : 344384 ≤ i.val := by
    unfold referenceSetupRow at tagged
    dsimp only at tagged
    split_ifs at tagged <;> simp [xorRow] at tagged
    omega
  let key : Fin 512 := ⟨i.val - 344384, by have size := i.isLt; omega⟩
  have last : referenceSetupRow control i = #v[key.val, (control key)[0], (control key)[1],
      (control key)[2], (control key)[3], (control key)[4], (control key)[5], (control key)[6], 28] := by
    unfold referenceSetupRow
    dsimp only
    split_ifs <;> try omega
    rfl
  refine ⟨key, ?_, ?_⟩
  · have equation := column 0 (by decide)
    rw [last] at equation
    simpa only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] using equation
  · intro j
    have equation := column (j.val + 1) (by have size := j.isLt; omega)
    rw [last] at equation
    fin_cases j <;> simpa using equation

end Airbender.Blake2G.Proofs
