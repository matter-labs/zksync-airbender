import Slop.Bigint.AdditiveGates
import Slop.Arithmetic.CarryChain

namespace Airbender.Bigint.Additive.Proofs
open Arithmetic
open scoped BigOperators
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem value_limbSum (limbs : Vector Nat 16) :
    value limbs = limbSum limbBase 16 (fun i => limbs[Fin.ofNat 16 i]) := by
  unfold value limbSum
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  congr 1
  apply Fin.ext
  simp

theorem natural_steps {p : Nat} [Fact p.Prime] (hp : 131072 ≤ p)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p} {input : Input} {output : Output}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (mapping : Mapping input output w) (bounds : InterfaceAssumptions input output w) :
    ∀ i : Fin 16,
      let incoming := (w (carryColumn i.val)).val
      let outgoing := (w (83 + i.val)).val
      match input.operation with
      | .add => input.left[i] + input.right[i] + incoming = output.result[i] + limbBase * outgoing
      | .sub => output.result[i] + input.right[i] + incoming = input.left[i] + limbBase * outgoing
      | .reverseSub => output.result[i] + input.left[i] + incoming = input.right[i] + limbBase * outgoing
      | .copy => input.right[i] + incoming = output.result[i] + limbBase * outgoing := by
  intro i
  have gates := native_steps (by omega) input.operation h mapping.selected i
  have result := native_results (by omega) input.operation h mapping.selected i
  have ranged := result_ranges h i
  rw [result.1] at ranged
  have written : output.result[i] = (w (67 + i.val)).val := by rw [mapping.result i, result.2]
  have outgoing := boolean_val (carry_bits h i)
  have incoming : (w (carryColumn i.val)).val ≤ 1 := by
    by_cases first : i.val = 0
    · simp only [carryColumn, first, ↓reduceIte, mapping.carry]
      split <;> simp [ZMod.val_one]
    · have prior := boolean_val (carry_bits h ⟨i.val - 1, by have := i.isLt; omega⟩)
      simpa only [carryColumn, first, ↓reduceIte, show 83 + (i.val - 1) = 82 + i.val by omega] using prior
  have left := bounds.1 i
  have right := bounds.2 i
  rw [mapping.left i] at left
  rw [mapping.right i] at right
  simp only [limbBase] at ranged left right ⊢
  rw [mapping.left i, mapping.right i, written]
  cases operationEq : input.operation
  all_goals simp only [operationEq] at gates ⊢
  · exact bounded_carry_step (F := ZMod p) hp left right ranged incoming outgoing (by simpa using gates)
  · exact bounded_carry_step (F := ZMod p) hp ranged right left incoming outgoing (by simpa using gates)
  · exact bounded_carry_step (F := ZMod p) hp ranged left right incoming outgoing (by simpa using gates)
  · have lifted := bounded_carry_step (F := ZMod p) hp (a := 0) (by omega) right ranged incoming outgoing
      (by simpa using gates)
    simpa using lifted

theorem soundness {p : Nat} [Fact p.Prime] (hp : 131072 ≤ p)
    (setup : Table (ZMod p) (fields 3)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := by
  intro input output w ⟨bounds, h, mapping⟩
  let carry : Nat → Nat := fun i => (w (carryColumn i)).val
  have incoming : carry 0 = input.carry.toNat := by
    simp only [carry, carryColumn, ↓reduceIte, mapping.carry]
    cases input.carry <;> simp [Bool.toNat, ZMod.val_one]
  have control := returned_control (by omega) input.operation h mapping.selected
  have returned : output.control.lo = carry 16 ∧ output.control.hi = 0 := by
    rw [mapping.control]
    simp [carry, carryColumn, control.1, control.2]
  have controlBound : output.control.lo ≤ 1 := by
    rw [returned.1]
    exact boolean_val (carry_bits h 15)
  have resultBound : ∀ i : Fin 16, output.result[i] < limbBase := by
    intro i
    have eqs := native_results (by omega) input.operation h mapping.selected i
    rw [mapping.result i, eqs.2, ← eqs.1]
    exact result_ranges h i
  refine ⟨resultBound, controlBound, returned.2, ?_⟩
  have steps := natural_steps hp h mapping bounds
  let left : Nat → Nat := fun i => input.left[Fin.ofNat 16 i]
  let right : Nat → Nat := fun i => input.right[Fin.ofNat 16 i]
  let result : Nat → Nat := fun i => output.result[Fin.ofNat 16 i]
  have recurrence (i : Nat) (hi : i < 16) := steps ⟨i, hi⟩
  have radix : limbBase ^ 16 = 2 ^ 256 := by decide
  cases operationEq : input.operation
  · have chain := carry_chain (left := left) (right := right) (result := result) (carry := carry)
      (length := 16) (radix := limbBase) (by
        intro i hi
        simpa [left, right, result, carry, Fin.ofNat_eq_cast, Nat.mod_eq_of_lt hi,
          carryColumn, show i + 1 ≠ 0 by omega, show 82 + (i + 1) = 83 + i by omega, operationEq] using recurrence i hi)
    simpa only [spec, operationEq, left, right, result, ← value_limbSum, incoming,
      radix, ← returned.1] using chain
  · have chain := carry_chain (left := result) (right := right) (result := left) (carry := carry)
      (length := 16) (radix := limbBase) (by
        intro i hi
        simpa [left, right, result, carry, Fin.ofNat_eq_cast, Nat.mod_eq_of_lt hi,
          carryColumn, show i + 1 ≠ 0 by omega, show 82 + (i + 1) = 83 + i by omega, operationEq] using recurrence i hi)
    simpa only [spec, operationEq, left, right, result, ← value_limbSum, incoming,
      radix, ← returned.1] using chain
  · have chain := carry_chain (left := result) (right := left) (result := right) (carry := carry)
      (length := 16) (radix := limbBase) (by
        intro i hi
        simpa [left, right, result, carry, Fin.ofNat_eq_cast, Nat.mod_eq_of_lt hi,
          carryColumn, show i + 1 ≠ 0 by omega, show 82 + (i + 1) = 83 + i by omega, operationEq] using recurrence i hi)
    simpa only [spec, operationEq, left, right, result, ← value_limbSum, incoming,
      radix, ← returned.1] using chain
  · have chain := carry_chain (left := fun _ => 0) (right := right) (result := result) (carry := carry)
      (length := 16) (radix := limbBase) (by
        intro i hi
        simpa [right, result, carry, Fin.ofNat_eq_cast, Nat.mod_eq_of_lt hi,
          carryColumn, show i + 1 ≠ 0 by omega, show 82 + (i + 1) = 83 + i by omega, operationEq] using recurrence i hi)
    have zero : limbSum limbBase 16 (fun _ => 0) = 0 := by simp [limbSum]
    simpa only [spec, operationEq, right, result, zero, zero_add, ← value_limbSum,
      incoming, radix, ← returned.1] using chain

end Airbender.Bigint.Additive.Proofs
