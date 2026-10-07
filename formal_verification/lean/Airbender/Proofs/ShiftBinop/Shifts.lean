import Airbender.Review.ShiftBinop.Artifact
import Airbender.Review.Properties
import Airbender.Proofs.ShiftBinop.Arithmetic
import Airbender.Proofs.Constraints

namespace Airbender.ShiftBinop.Proofs
open Airbender.Arithmetic

private theorem shift_wiring {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 1 ∧ w 12 = 0) (i : Fin 4) :
    ∀ j : Fin 9, w (56 + 9 * i.val + j.val) =
      (#v[(i.val : ZMod p), w (19 + i.val), w 35 + w 8, w 10,
        w (36 + 4 * i.val), w (37 + 4 * i.val), w (38 + 4 * i.val),
        w (39 + 4 * i.val), 9] : Vector (ZMod p) 9)[j.val] := by
  intro j
  have equation := Verification.assertion_of_holds h
    ⟨5 + 9 * i.val + j.val, by rw [constraint_count]; have := i.isLt; have := j.isLt; omega⟩
  fin_cases i <;> fin_cases j <;>
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected.1, selected.2] at equation ⊢
  all_goals linear_combination equation

/-- The selected imported query truncates rs2's first byte, without an assumed
    bound on that byte or on its truncation scratch variable. -/
theorem shift_amount {p : Nat} [Fact p.Prime] (hp : 256 < p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 1 ∧ w 12 = 0) :
    (w 25).val < 256 ∧ (w 26).val < 256 ∧ (w 35).val = (w 25).val % 32 := by
  have equations (i : Fin 4) := Verification.assertion_of_holds h
    ⟨1 + i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  have a := equations 0
  have b := equations 1
  have c := equations 2
  have tag := equations 3
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected.1, selected.2] at a b c tag
  have wa : w 52 = w 25 := by linear_combination a
  have wb : w 53 = w 26 := by linear_combination b
  have wc : w 54 = w 35 := by linear_combination c
  have wt : w 55 = 8 := by linear_combination tag
  have query := Verification.lookup_of_holds h ⟨2, by rw [lookup_count]; decide⟩
  have values := Verification.truncation_lookup hp query
    (by simpa [Expression.eval, Verification.environment] using wt)
  simpa [Expression.eval, Verification.environment, wa, wb, wc] using values

set_option maxHeartbeats 1000000 in
/-- Each selected shift query forces its four canonical contribution bytes,
    the shared amount and the operation tag. All wiring comes from JSON equations. -/
theorem shift_bytes {p : Nat} [Fact p.Prime] (hp : 256 < p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 1 ∧ w 12 = 0) :
    (w 35 + w 8).val < 32 ∧ (w 10).val < 8 ∧
    ∀ i j : Fin 4, (w (36 + 4 * i.val + j.val)).val =
      ((Verification.shiftByteContribution i.val (w (19 + i.val)).val
        (w 35 + w 8).val (w 10).val).extractLsb' (8 * j.val) 8).toNat := by
  have values (i : Fin 4) :
      (w 35 + w 8).val < 32 ∧ (w 10).val < 8 ∧
      ∀ j : Fin 4, (w (36 + 4 * i.val + j.val)).val =
        ((Verification.shiftByteContribution i.val (w (19 + i.val)).val
          (w 35 + w 8).val (w 10).val).extractLsb' (8 * j.val) 8).toNat := by
    have wires := shift_wiring h selected i
    have query := Verification.lookup_of_holds h
      ⟨3 + i.val, by rw [lookup_count]; have := i.isLt; omega⟩
    have position : ((i.val : ZMod p)).val = i.val := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
    fin_cases i
    all_goals
      have a := wires 0
      have b := wires 1
      have c := wires 2
      have d := wires 3
      have tag := wires 8
      norm_num [Fin.val_zero, Fin.val_one, Fin.val_ofNat] at a b c d tag position
      have result := Verification.shift_lookup hp query
        (by simpa [Expression.eval, Verification.environment] using tag)
      refine ⟨?_, ?_, ?_⟩
      · simpa [Expression.eval, Verification.environment, c] using result.2.2.1
      · simpa [Expression.eval, Verification.environment, d] using result.2.2.2.1
      intro j
      have output := result.2.2.2.2 j
      have wire := wires ⟨4 + j.val, by have := j.isLt; omega⟩
      fin_cases j <;>
        norm_num [Fin.val_zero, Fin.val_one, Fin.val_ofNat] at wire
      all_goals simpa [Expression.eval, Verification.environment, a, b, c, d, position, wire] using output
  exact ⟨(values 0).1, (values 0).2.1, fun i j => (values i).2.2 j⟩

private theorem packed_contributions {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    (w : Nat → ZMod p) (start : Nat) (target : ZMod p)
    (bounds : ∀ i : Fin 4, ∀ j : Fin 2, (w (start + 4 * i.val + j.val)).val < 256)
    (equation : w start + 256 * w (start + 1) + w (start + 4) + 256 * w (start + 5) +
      w (start + 8) + 256 * w (start + 9) + w (start + 12) + 256 * w (start + 13) - target = 0) :
    target.val = (w start).val + 256 * (w (start + 1)).val +
      (w (start + 4)).val + 256 * (w (start + 5)).val +
      (w (start + 8)).val + 256 * (w (start + 9)).val +
      (w (start + 12)).val + 256 * (w (start + 13)).val := by
  let total := (w start).val + 256 * (w (start + 1)).val +
    (w (start + 4)).val + 256 * (w (start + 5)).val +
    (w (start + 8)).val + 256 * (w (start + 9)).val +
    (w (start + 12)).val + 256 * (w (start + 13)).val
  have field : target = (total : ZMod p) := by
    dsimp [total]
    push_cast
    simp only [ZMod.natCast_zmod_val]
    linear_combination -equation
  have small : total < p := by
    have a : (w start).val < 256 := bounds 0 0
    have b : (w (start + 1)).val < 256 := bounds 0 1
    have c : (w (start + 4)).val < 256 := bounds 1 0
    have d : (w (start + 5)).val < 256 := bounds 1 1
    have e : (w (start + 8)).val < 256 := bounds 2 0
    have f : (w (start + 9)).val < 256 := bounds 2 1
    have g : (w (start + 12)).val < 256 := bounds 3 0
    have h : (w (start + 13)).val < 256 := bounds 3 1
    dsimp [total]
    omega
  rw [field, ZMod.val_natCast, Nat.mod_eq_of_lt small]

/-- Imported shift lookups and assembly equations force the native shifted word.
    The decoder supplies the operation code; source-byte mapping supplies only
    the operand, and no result or scratch bounds are assumed. -/
theorem shift_destination {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    {w : Nat → ZMod p} (x : BitVec 32)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 1 ∧ w 12 = 0)
    (operation : (w 10).val = 1 ∨ (w 10).val = 2 ∨ (w 10).val = 3 ∨ (w 10).val = 5)
    (reverse : (w 10).val = 5 → (w 35 + w 8).val = 0)
    (operand : ∀ i : Fin 4, w (19 + i.val) =
      ((x.extractLsb' (8 * i.val) 8).toNat : ZMod p)) :
    (Word.mk (w 31).val (w 32).val).toBitVec =
      Verification.shiftOperation (w 10).val x (w 35 + w 8).val := by
  have bytes := (shift_bytes (by omega) h selected).2.2
  let contribution (i : Fin 4) := Verification.shiftByteContribution i.val
    (w (19 + i.val)).val (w 35 + w 8).val (w 10).val
  have bounds (i j : Fin 4) : (w (36 + 4 * i.val + j.val)).val < 256 := by
    rw [bytes i j]
    exact (contribution i |>.extractLsb' (8 * j.val) 8).isLt
  have low := Verification.assertion_of_holds h ⟨41, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨42, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected.1, selected.2] at low high
  have lo := packed_contributions hp w 36 (w 31)
    (fun i j => bounds i ⟨j.val, by have := j.isLt; omega⟩)
    (by linear_combination low)
  have hi := packed_contributions hp w 38 (w 32)
    (by
      intro i j
      have same : 36 + 4 * i.val + (2 + j.val) = 38 + 4 * i.val + j.val := by omega
      simpa only [same] using bounds i ⟨2 + j.val, by have := j.isLt; omega⟩)
    (by linear_combination high)
  have rebuild (i : Fin 4) : (contribution i).toNat =
      (w (36 + 4 * i.val)).val + 256 * (w (37 + 4 * i.val)).val +
      65536 * (w (38 + 4 * i.val)).val + 16777216 * (w (39 + 4 * i.val)).val := by
    have b0 : (w (36 + 4 * i.val)).val = ((contribution i).extractLsb' 0 8).toNat := by
      simpa [contribution] using bytes i 0
    have b1 : (w (37 + 4 * i.val)).val = ((contribution i).extractLsb' 8 8).toNat := by
      have same : 36 + 4 * i.val + 1 = 37 + 4 * i.val := by omega
      simpa [contribution, same] using bytes i 1
    have b2 : (w (38 + 4 * i.val)).val = ((contribution i).extractLsb' 16 8).toNat := by
      have same : 36 + 4 * i.val + 2 = 38 + 4 * i.val := by omega
      simpa [contribution, same] using bytes i 2
    have b3 : (w (39 + 4 * i.val)).val = ((contribution i).extractLsb' 24 8).toNat := by
      have same : 36 + 4 * i.val + 3 = 39 + 4 * i.val := by omega
      simpa [contribution, same] using bytes i 3
    rw [b0, b1, b2, b3]
    exact bytes_value (contribution i)
  have mapped (i : Fin 4) : (w (19 + i.val)).val = (x.extractLsb' (8 * i.val) 8).toNat := by
    have bound := (x.extractLsb' (8 * i.val) 8).isLt
    rw [operand i, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have combined : (contribution 0).toNat + (contribution 1).toNat +
      (contribution 2).toNat + (contribution 3).toNat =
      (Verification.shiftOperation (w 10).val x (w 35 + w 8).val).toNat := by
    simp only [contribution, mapped]
    exact (Verification.shift_contributions_value _ operation x _ reverse).symm
  apply BitVec.eq_of_toNat_eq
  change ((w 31).val + limbBase * (w 32).val) % wordModulus = _
  have value : (w 31).val + limbBase * (w 32).val =
      (Verification.shiftOperation (w 10).val x (w 35 + w 8).val).toNat := by
    rw [← combined, lo, hi, rebuild 0, rebuild 1, rebuild 2, rebuild 3]
    norm_num [limbBase, Fin.val_zero, Fin.val_one, Fin.val_ofNat]
    ring
  rw [value]
  exact Nat.mod_eq_of_lt (Verification.shiftOperation _ x _).isLt

end Airbender.ShiftBinop.Proofs
