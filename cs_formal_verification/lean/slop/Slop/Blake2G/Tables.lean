module
public import Human.Circuits.Blake2G.Tables.Setup
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Airbender.Blake2G.Proofs

private abbrev xorTags : Vector Nat 5 := #v[4, 17, 18, 19, 20]

private abbrev xorWidths : Vector Nat 5 := #v[8, 3, 4, 7, 9]

private theorem tags_injective (a b : Fin 5) (same : xorTags[a] = xorTags[b]) : a = b := by
  fin_cases a <;> fin_cases b <;> first | rfl | simp at same

private theorem tags_small : ∀ kind : Fin 5, xorTags[kind] ≤ 20 := by decide

set_option maxRecDepth 100000 in
/-- Every setup row, by region: a sized XOR row, or the controller region (tag 28). -/
private theorem row_cases {control : Fin 512 → Vector Nat 7} (index : Fin 344896) :
    (∃ kind : Fin 5, (setupRow control index)[8] = xorTags[kind] ∧
      (setupRow control index)[0] < 2 ^ xorWidths[kind] ∧
      (setupRow control index)[1] < 2 ^ xorWidths[kind] ∧
      (setupRow control index)[2] = (setupRow control index)[0] ^^^ (setupRow control index)[1]) ∨
    ((setupRow control index)[8] = 28 ∧ 344384 ≤ index.val) := by
  have size := index.isLt
  unfold setupRow
  dsimp only
  split_ifs
  · exact Or.inl ⟨0, by simp [xorRow]; omega⟩
  · exact Or.inl ⟨1, by simp [xorRow]; omega⟩
  · exact Or.inl ⟨2, by simp [xorRow]; omega⟩
  · exact Or.inl ⟨3, by simp [xorRow]; omega⟩
  · exact Or.inl ⟨4, by simp [xorRow]; omega⟩
  · exact Or.inr ⟨rfl, by omega⟩

private theorem xor_rows {control : Fin 512 → Vector Nat 7} (index : Fin 344896)
    (kind : Fin 5) (selected : (setupRow control index)[8] = (#v[4, 17, 18, 19, 20][kind])) :
    (setupRow control index)[0] < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (setupRow control index)[1] < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (setupRow control index)[2] =
      (setupRow control index)[0] ^^^ (setupRow control index)[1] := by
  rcases row_cases (control := control) index with ⟨other, tag, a, b, xor⟩ | ⟨tag, _⟩
  · obtain rfl := tags_injective other kind (tag.symm.trans selected)
    exact ⟨a, b, xor⟩
  · have := tags_small kind
    simp only [xorTags] at this
    omega

/-- The tag of every setup row is at most 28. -/
private theorem row_tag_le {control : Fin 512 → Vector Nat 7} (index : Fin 344896) :
    (setupRow control index)[8] ≤ 28 := by
  rcases row_cases (control := control) index with ⟨kind, tag, _⟩ | ⟨tag, _⟩
  · have := tags_small kind
    omega
  · omega

/-- Each selected XOR region in the native static table enforces its chunk bounds
    and exact XOR. This uses table membership, not an assumed circuit result. -/
theorem xor_lookup {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
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
  obtain ⟨i, row⟩ := member
  have column (j : Nat) (hj : j < 9) :
      entry[j].eval env = ((setupRow control i)[j] : ZMod p) := by
    have equation := congrArg (fun (v : Vector (ZMod p) 9) => v[j]) row
    simpa only [Vector.getElem_map] using equation
  have tagBound : (setupRow control i)[8] < p := by
    have := row_tag_le (control := control) i
    omega
  have wantedBound : (#v[4, 17, 18, 19, 20][kind] : Nat) < p := by
    fin_cases kind <;> dsimp <;> omega
  have tagged : (setupRow control i)[8] = (#v[4, 17, 18, 19, 20][kind]) := by
    have equation := congrArg ZMod.val ((column 8 (by decide)).symm.trans selected)
    simp only [ZMod.val_natCast] at equation
    rw [Nat.mod_eq_of_lt tagBound, Nat.mod_eq_of_lt wantedBound] at equation
    exact equation
  obtain ⟨a, b, xor⟩ := xor_rows i kind tagged
  have c : (setupRow control i)[2] < 2 ^ (#v[8, 3, 4, 7, 9][kind]) := by
    rw [xor]
    exact Nat.xor_lt_two_pow a b
  have widthBound : 2 ^ (#v[8, 3, 4, 7, 9][kind]) ≤ 512 := by fin_cases kind <;> norm_num
  have value (j : Nat) (hj : j < 9) (bound : (setupRow control i)[j] < 2 ^ (#v[8, 3, 4, 7, 9][kind])) :
      (entry[j].eval env).val = (setupRow control i)[j] := by
    rw [column j hj]
    exact ZMod.val_natCast_of_lt (by omega)
  rw [value 0 (by decide) a, value 1 (by decide) b, value 2 (by decide) c]
  exact ⟨a, b, c, xor⟩

set_option maxRecDepth 4096 in
/-- Tag 28 selects the controller region and binds every output column to one
    supplied row. No assumptions about that row's behavior are used here. -/
theorem control_lookup {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {control : Fin 512 → Vector Nat 7} {entry : Vector (Expression (ZMod p)) 9}
    {env : Environment (ZMod p)}
    (h : (Lookup.mk (setupTable control).toRaw entry).Contains env)
    (selected : entry[8].eval env = 28) :
    ∃ key : Fin 512, entry[0].eval env = (key.val : ZMod p) ∧
      ∀ j : Fin 7, entry[j.val + 1].eval env = ((control key)[j] : ZMod p) := by
  have member := (Lookup.mk (setupTable control).toRaw entry).table.imply_soundness _ _ h
  change ∃ i : Fin 344896, entry.map (Expression.eval env) =
    (setupRow control i).map (fun (n : Nat) => (n : ZMod p)) at member
  obtain ⟨i, row⟩ := member
  have column (j : Nat) (hj : j < 9) :
      entry[j].eval env = ((setupRow control i)[j] : ZMod p) := by
    have equation := congrArg (fun (v : Vector (ZMod p) 9) => v[j]) row
    simpa only [Vector.getElem_map] using equation
  have tagBound : (setupRow control i)[8] < p := by
    have := row_tag_le (control := control) i
    omega
  have tagged : (setupRow control i)[8] = 28 := by
    have equation := congrArg ZMod.val ((column 8 (by decide)).symm.trans selected)
    have literal : (28 : ZMod p).val = 28 := by
      change ((28 : Nat) : ZMod p).val = 28
      exact ZMod.val_natCast_of_lt (by omega)
    rw [ZMod.val_natCast_of_lt tagBound, literal] at equation
    exact equation
  have region : 344384 ≤ i.val := by
    rcases row_cases (control := control) i with ⟨kind, tag, _⟩ | ⟨_, region⟩
    · have := tags_small kind
      omega
    · exact region
  let key : Fin 512 := ⟨i.val - 344384, by have size := i.isLt; omega⟩
  have last : setupRow control i = #v[key.val, (control key)[0], (control key)[1],
      (control key)[2], (control key)[3], (control key)[4], (control key)[5], (control key)[6], 28] := by
    unfold setupRow
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
