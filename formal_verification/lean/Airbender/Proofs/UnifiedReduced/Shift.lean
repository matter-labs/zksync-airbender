import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.UnifiedReduced.Binary
import Airbender.Proofs.Arithmetic.WordBytes
import Airbender.Proofs.Arithmetic.ShiftAssembly

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

private theorem shift_wiring [Fact p.Prime] {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 26 = 1 ∧ w 27 = 0) (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (i : Fin 4) : w (86 + 9 * i.val) = 9 ∧ ∀ j : Fin 8, w (87 + 9 * i.val + j.val) =
      (#v[(i.val : ZMod p), leftByte w i, w 57 + w 8, w 10,
        w (58 + 4 * i.val), w (59 + 4 * i.val), w (60 + 4 * i.val), w (61 + 4 * i.val)] : Vector (ZMod p) 8)[j] := by
  have h (j : Fin 9) := Verification.assertion_of_holds holds
    ⟨49 + 9 * i.val + j.val, by rw [constraint_count]; have := i.isLt; have := j.isLt; omega⟩
  constructor
  · have t := h 0
    fin_cases i
    all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
      selected.1, selected.2, other.1, other.2.1, other.2.2.1, other.2.2.2] at t ⊢
    all_goals linear_combination t
  · intro j
    have equation := h ⟨1 + j.val, by have := j.isLt; omega⟩
    fin_cases i <;> fin_cases j
    all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
      selected.1, selected.2, other.1, other.2.1, other.2.2.1, other.2.2.2, leftByte] at equation ⊢
    all_goals linear_combination equation

theorem shift_query_values [Fact p.Prime] (hp : FieldCapacity.NoWrap p 256)
    {initial : Reference.RiscV.Sail.State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table initial)))
    (selected : w 26 = 1 ∧ w 27 = 0) (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0) :
    (w 57 + w 8).val < 32 ∧ (w 10).val < 8 ∧
    (∀ i : Fin 4, (leftByte w i).val < 256) ∧
    ∀ i j : Fin 4, (w (58 + 4 * i.val + j.val)).val =
      ((Verification.shiftByteContribution i.val (leftByte w i).val
        (w 57 + w 8).val (w 10).val).extractLsb' (8 * j.val) 8).toNat := by
  have values (i : Fin 4) : (w 57 + w 8).val < 32 ∧ (w 10).val < 8 ∧
      (leftByte w i).val < 256 ∧ ∀ j : Fin 4, (w (58 + 4 * i.val + j.val)).val =
        ((Verification.shiftByteContribution i.val (leftByte w i).val
          (w 57 + w 8).val (w 10).val).extractLsb' (8 * j.val) 8).toNat := by
    have wires := shift_wiring holds selected other i
    have query := Verification.lookup_of_holds holds ⟨14 + i.val, by rw [lookup_count]; have := i.isLt; omega⟩
    have a := wires.2 0; have b := wires.2 1; have c := wires.2 2; have d := wires.2 3
    have position : ((i.val : ZMod p)).val = i.val := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
    fin_cases i
    all_goals
      have standard := Setup.Proofs.ordinary_lookup (by omega : 55 ≤ p) query 9 (Or.inr (Or.inr rfl))
        (by simpa [Expression.eval, Verification.environment] using wires.1)
      have result := Verification.shift_lookup hp standard
        (by simpa [Expression.eval, Verification.environment] using wires.1)
    all_goals norm_num [Fin.val_zero, Fin.val_one, Fin.val_ofNat] at a b c d position
    all_goals refine ⟨?_, ?_, ?_, ?_⟩
    all_goals first
      | simpa [Expression.eval, Verification.environment, c] using result.2.2.1
      | simpa [Expression.eval, Verification.environment, d] using result.2.2.2.1
      | simpa [Expression.eval, Verification.environment, b, leftByte] using result.2.1
      | (intro j
         have output := result.2.2.2.2 j
         have wire := wires.2 ⟨4 + j.val, by have := j.isLt; omega⟩
         fin_cases j
         all_goals norm_num [Fin.val_zero, Fin.val_one, Fin.val_ofNat] at wire
         all_goals simpa [Expression.eval, Verification.environment, a, b, c, d, position, wire, leftByte] using output)
  exact ⟨(values 0).1, (values 0).2.1, fun i => (values i).2.2.1, fun i j => (values i).2.2.2 j⟩

theorem shift_left_bytes [Fact p.Prime] (hp : FieldCapacity.NoWrap p 65536)
    (inverse : SerializedInverse.Scale256 p)
    {initial : Reference.RiscV.Sail.State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table initial)))
    (selected : w 26 = 1 ∧ w 27 = 0) (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0) :
    ∀ i : Fin 4, leftByte w i =
      (((Word.mk (w 36).val (w 37).val).toBitVec.extractLsb' (8 * i.val) 8).toNat : ZMod p) := by
  exact Word.byte_fields hp (w 36) (w 37) (leftByte w) (shift_query_values (by omega) holds selected other).2.2.1
    (by change w 74 + 256 * (-7864320 * (w 36 - w 74)) = w 36
        linear_combination (w 36 - w 74) * inverse)
    (by change w 75 + 256 * (-7864320 * (w 37 - w 75)) = w 37
        linear_combination (w 37 - w 75) * inverse)

theorem shift_amount [Fact p.Prime] (hp : FieldCapacity.NoWrap p 256)
    {initial : Reference.RiscV.Sail.State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table initial)))
    (selected : w 26 = 1 ∧ w 27 = 0) (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (load : w 28 = 0) :
    (w 76).val < 256 ∧ (-7864320 * (w 42 - w 76)).val < 256 ∧ (w 57).val = (w 76).val % 32 := by
  have gate := Verification.assertion_of_holds holds ⟨39, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, load] at gate
  have h (i : Fin 4) := Verification.assertion_of_holds holds ⟨45 + i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  have t := h 0; have a := h 1; have b := h 2; have c := h 3
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected.1, selected.2, other.1, other.2.1, other.2.2.1, other.2.2.2, gate] at t a b c
  have tag : w 82 = 8 := by linear_combination t
  have first : w 83 = w 76 := by linear_combination a
  have second : w 84 = -7864320 * (w 42 - w 76) := by linear_combination b
  have amount : w 85 = w 57 := by linear_combination c
  have query := Verification.lookup_of_holds holds ⟨13, by rw [lookup_count]; decide⟩
  have standard := Setup.Proofs.ordinary_lookup (by omega : 55 ≤ p) query 8 (Or.inr (Or.inl rfl))
    (by simpa [Expression.eval, Verification.environment] using tag)
  have result := Verification.truncation_lookup hp standard
    (by simpa [Expression.eval, Verification.environment] using tag)
  simpa [Expression.eval, Verification.environment, first, second, amount] using result

theorem shift_destination [Fact p.Prime] (hp : FieldCapacity.NoWrap p 262144)
    {initial : Reference.RiscV.Sail.State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table initial)))
    (selected : w 26 = 1 ∧ w 27 = 0) (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (x : BitVec 32) (operand : ∀ i : Fin 4, leftByte w i = ((x.extractLsb' (8 * i.val) 8).toNat : ZMod p))
    (operation : (w 10).val = 1 ∨ (w 10).val = 2 ∨ (w 10).val = 3 ∨ (w 10).val = 5)
    (reverse : (w 10).val = 5 → (w 57 + w 8).val = 0) :
    (Word.mk (w 50).val (w 51).val).toBitVec = Verification.shiftOperation (w 10).val x (w 57 + w 8).val := by
  have queries := shift_query_values (by omega) holds selected other
  have bytes := queries.2.2.2
  have small (i j : Fin 4) : (w (58 + 4 * i.val + j.val)).val < 256 := by
    rw [bytes i j]
    exact ((Verification.shiftByteContribution i.val (leftByte w i).val
      (w 57 + w 8).val (w 10).val).extractLsb' (8 * j.val) 8).isLt
  have low := Verification.assertion_of_holds holds ⟨24, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds holds ⟨25, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected.1, selected.2] at low high
  have lo := Verification.sum_byte_pairs hp (fun i j => w (58 + 4 * i.val + j.val)) (w 50)
    (fun i j => small i ⟨j.val, by have := j.isLt; omega⟩) (by linear_combination low)
  have hi := Verification.sum_byte_pairs hp (fun i j => w (60 + 4 * i.val + j.val)) (w 51)
    (by intro i j; simpa only [show 58 + 4 * i.val + (2 + j.val) = 60 + 4 * i.val + j.val by omega]
          using small i ⟨2 + j.val, by have := j.isLt; omega⟩) (by linear_combination high)
  apply Verification.shift_assembly (w 10).val operation x (w 57 + w 8).val reverse
    (fun i j => (w (58 + 4 * i.val + j.val)).val) (Word.mk (w 50).val (w 51).val)
  · intro i j
    rw [bytes i j, operand i, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := (x.extractLsb' (8 * i.val) 8).isLt; omega)]
  · exact lo
  · exact hi

end Airbender.UnifiedReduced.Proofs
