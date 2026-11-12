module
public import Slop.Bigint.Shapes
public import Human.Circuits.Bigint.Tables.Setup
public import Human.Circuits.Bigint.Artifact
public import Slop.Lookups
public import Slop.Constraints
public import Slop.Arithmetic.Lemmas
public import Human.Helpers.Properties
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

namespace Airbender.Bigint.Proofs
set_option warningAsError true

/-- Every setup row, by region: a carry range (tags 22 to 26) or a low byte (tag 41). -/
theorem row_cases (index : Fin 1390592) :
    (22 ≤ (setupRow index).2.2 ∧ (setupRow index).2.2 ≤ 26 ∧
      (setupRow index).1 < 2 ^ ((setupRow index).2.2 - 13) ∧
      (setupRow index).2.1 < 2 ^ ((setupRow index).2.2 - 13)) ∨
    ((setupRow index).2.2 = 41 ∧ (setupRow index).1 < 65536 ∧
      (setupRow index).2.1 = (setupRow index).1 % 256) := by
  have size := index.isLt
  unfold setupRow
  dsimp only
  split_ifs <;> dsimp only <;> simp only [Nat.reduceSub, Nat.reducePow, true_and, and_true] <;>
    omega

private theorem low_byte_rows (index : Fin 1390592) (selected : (setupRow index).2.2 = 41) :
    (setupRow index).1 < 65536 ∧ (setupRow index).2.1 = (setupRow index).1 % 256 := by
  rcases row_cases index with range | low
  · omega
  · exact low.2

/-- Decode a native membership witness into its natural setup row. -/
theorem fixed_row_values {p tag : Nat} [Fact p.Prime] (hp : 65536 ≤ p) (tagBound : tag < p)
    {entry : Vector (Expression (ZMod p)) 3} {env : Environment (ZMod p)}
    (h : (Lookup.mk setupTable.toRaw entry).Contains env)
    (selected : entry[(2 : Nat)].eval env = (tag : ZMod p)) :
    ∃ i : Fin 1390592, entry[0].eval env = ((setupRow i).1 : ZMod p) ∧
      entry[1].eval env = ((setupRow i).2.1 : ZMod p) ∧ (setupRow i).2.2 = tag := by
  change ∃ i : Fin 1390592, entry.map (Expression.eval env) =
    #v[((setupRow i).1 : ZMod p), ((setupRow i).2.1 : ZMod p), ((setupRow i).2.2 : ZMod p)] at h
  obtain ⟨i, row⟩ := h
  have key : entry[0].eval env = ((setupRow i).1 : ZMod p) := by
    have eq := congrArg (fun v : Vector (ZMod p) 3 => v[(0 : Nat)]) row
    simpa only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero] using eq
  have low : entry[1].eval env = ((setupRow i).2.1 : ZMod p) := by
    have eq := congrArg (fun v : Vector (ZMod p) 3 => v[(1 : Nat)]) row
    simpa only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_succ, List.getElem_cons_zero] using eq
  have tagField : entry[2].eval env = ((setupRow i).2.2 : ZMod p) := by
    have eq := congrArg (fun v : Vector (ZMod p) 3 => v[(2 : Nat)]) row
    simpa only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_succ, List.getElem_cons_zero] using eq
  have rowTagBound : (setupRow i).2.2 < p := by
    rcases row_cases i with range | low <;> omega
  have tagEq : (setupRow i).2.2 = tag := by
    have eq := congrArg ZMod.val (tagField.symm.trans selected)
    have literal : (tag : ZMod p).val = tag := by
      exact ZMod.val_natCast_of_lt tagBound
    rw [ZMod.val_natCast_of_lt rowTagBound, literal] at eq
    exact eq
  exact ⟨i, key, low, tagEq⟩

/-- Project tag 41 into U16GetLowByte rows and reuse the shared row-value
    theorem for its range and low byte. Clean supplies native membership. -/
theorem low_byte_value {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    {entry : Vector (Expression (ZMod p)) 3} {env : Environment (ZMod p)}
    (h : (Lookup.mk setupTable.toRaw entry).Contains env)
    (selected : entry[(2 : Nat)].eval env = 41) :
    (entry[(0 : Nat)].eval env).val < 65536 ∧
      entry[(1 : Nat)].eval env = (((entry[(0 : Nat)].eval env).val % 256 : Nat) : ZMod p) := by
  obtain ⟨i, key, low, tag⟩ := fixed_row_values hp (tag := 41) (by omega) h selected
  obtain ⟨keyBound, lowValue⟩ := low_byte_rows i tag
  apply Verification.pair_value_of_row (value := fun n => n % 256) hp
  refine ⟨⟨(setupRow i).1, keyBound⟩, Prod.ext key ?_⟩
  simpa only [lowValue] using low

/-- Both low-byte queries of source limb `i` (lookups `34 + i` and `50 + i`), read once for every
    limb. -/
theorem low_byte_pairs {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (i : Fin 16) :
    ((w Variables.leftLimbs[i]).val < 65536 ∧
      w (99 + i.val) = (((w Variables.leftLimbs[i]).val % 256 : Nat) : ZMod p)) ∧
    ((w Variables.rightLimbs[i]).val < 65536 ∧
      w (115 + i.val) = (((w Variables.rightLimbs[i]).val % 256 : Nat) : ZMod p)) := by
  obtain ⟨leftShape, rightShape⟩ := Shapes.low_byte_shape (p := p) setupTable i
  have left := Verification.lookup_of_holds h ⟨34 + i.val,
    by rw [lookup_count]; have := i.isLt; omega⟩
  have right := Verification.lookup_of_holds h ⟨50 + i.val,
    by rw [lookup_count]; have := i.isLt; omega⟩
  rw [leftShape] at left
  rw [rightShape] at right
  have tag := Templates.tag_eval w 41
  rw [Nat.cast_ofNat] at tag
  have leftPair := low_byte_value hp left tag
  have rightPair := low_byte_value hp right tag
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, Templates.entry_eval] at leftPair rightPair
  rw [Shapes.left_column, Shapes.right_column]
  exact ⟨leftPair, rightPair⟩

theorem source_ranges {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    ∀ i : Fin 16, (w Variables.leftLimbs[i]).val < Arithmetic.limbBase ∧
      (w Variables.rightLimbs[i]).val < Arithmetic.limbBase :=
  fun i => ⟨(low_byte_pairs hp h i).1.1, (low_byte_pairs hp h i).2.1⟩

end Airbender.Bigint.Proofs
