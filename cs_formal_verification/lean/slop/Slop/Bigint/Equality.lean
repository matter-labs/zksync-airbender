import Slop.Bigint.EqualityGates
import Slop.Arithmetic.Digits

namespace Airbender.Bigint.Equality.Proofs
open Arithmetic
open scoped BigOperators
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private def carry {p : Nat} (w : Nat → ZMod p) (i : Nat) : Nat :=
  if i = 0 then 0 else (w (carryColumn i)).val

theorem carry_bounded {p : Nat} [Fact p.Prime]
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    ∀ i ≤ 16, carry w i ≤ 1 := by
  intro i hi
  by_cases first : i = 0
  · simp [carry, first]
  · have bounded := boolean_val (Additive.Proofs.carry_bits h ⟨i - 1, by omega⟩)
    simpa [carry, first, carryColumn, show 83 + (i - 1) = 82 + i by omega] using bounded

theorem result_ranges {p : Nat} [Fact p.Prime] (hp : 8 ≤ p)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 64 = 1) : ∀ i : Fin 16, (w (67 + i.val)).val < limbBase := by
  intro i
  have ranged := Additive.Proofs.result_ranges h i
  rw [(native_results hp h selected i).1] at ranged
  exact ranged

theorem natural_steps {p : Nat} [Fact p.Prime] (hp : 131072 ≤ p)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p} {input : Input} {output : Output}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (mapping : Mapping input output w) (bounds : InterfaceAssumptions input output w) :
    ∀ i : Fin 16, (w (67 + i.val)).val + input.right[i] + carry w i.val =
      input.left[i] + limbBase * carry w (i.val + 1) := by
  intro i
  have gate := native_steps (by omega) h mapping.selected i
  have ranged := result_ranges (by omega) h mapping.selected i
  have left := bounds.1 i
  have right := bounds.2 i
  have incoming := carry_bounded h i.val (by have := i.isLt; omega)
  have outgoing := carry_bounded h (i.val + 1) (by have := i.isLt; omega)
  apply bounded_carry_step (F := ZMod p) hp ranged right left incoming outgoing
  rw [mapping.left i, mapping.right i]
  simp only [ZMod.natCast_zmod_val]
  simp only [carry, carryColumn, show i.val + 1 ≠ 0 by omega, ↓reduceIte,
    show 82 + (i.val + 1) = 83 + i.val by omega]
  split_ifs with first <;> simpa [first, carryColumn, limbBase] using gate

theorem sum_zero_iff {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {setup : Table (ZMod p) (fields 3)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 64 = 1) : w 210 = 0 ↔ ∀ i : Fin 16, (w (67 + i.val)).val = 0 := by
  let total := ∑ i : Fin 16, (w (67 + i.val)).val
  have bounded : total ≤ 16 * 65535 := by
    calc
      _ ≤ ∑ _i : Fin 16, 65535 := Finset.sum_le_sum (by
        intro i _
        have range := result_ranges (by omega) h selected i
        simp only [limbBase] at range
        omega)
      _ = _ := by simp
  rw [native_sum (by omega) h selected]
  exact field_sum_zero (by change total < p; omega)

theorem soundness {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    (setup : Table (ZMod p) (fields 3)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := by
  intro input output w ⟨bounds, h, mapping⟩
  let left : Nat → Nat := fun i => input.left[Fin.ofNat 16 i]
  let right : Nat → Nat := fun i => input.right[Fin.ofNat 16 i]
  let result : Nat → Nat := fun i => (w (67 + i)).val
  have steps := natural_steps (by omega) h mapping bounds
  have ranged := result_ranges (by omega) h mapping.selected
  have difference := subtraction_zero (length := 16) (radix := limbBase)
    (left := left) (right := right) (result := result) (carry := carry w)
    (by intro i hi; simpa [left, right, result, Fin.ofNat_eq_cast, Nat.mod_eq_of_lt hi] using steps ⟨i, hi⟩)
    (fun i hi => ranged ⟨i, hi⟩)
    (by intro i hi; simpa [right, Fin.ofNat_eq_cast, Nat.mod_eq_of_lt hi] using bounds.2 ⟨i, hi⟩)
    (carry_bounded h) (by simp [carry])
  have zeroFinite : (∀ i : Fin 16, (w (67 + i.val)).val = 0) ↔ ∀ i < 16, result i = 0 := by
    constructor
    · intro zeros i hi; exact zeros ⟨i, hi⟩
    · intro zeros i; exact zeros i.val i.isLt
  have same : (∀ i < 16, left i = right i) ↔ input.left = input.right := by
    constructor
    · intro eqs
      apply Vector.ext
      intro i hi
      simpa [left, right, Fin.ofNat_eq_cast, Nat.mod_eq_of_lt hi] using eqs i hi
    · intro eqs i _
      simp [left, right, eqs]
  have equal : w 210 = 0 ↔ input.left = input.right :=
    (sum_zero_iff hp h mapping.selected).trans (zeroFinite.trans (difference.1.trans same))
  have preserved : output.result = input.left := by
    apply Vector.ext
    intro i hi
    have written := mapping.result ⟨i, hi⟩
    have original := mapping.left ⟨i, hi⟩
    have native := congrArg ZMod.val (native_results (by omega) h mapping.selected ⟨i, hi⟩).2
    simpa only [Fin.getElem_fin] using written.trans (native.trans original.symm)
  have response := native_control (by omega) h mapping.selected
  have flag := native_zero_check h
  refine ⟨preserved, ?_⟩
  rw [mapping.control, response.2]
  by_cases eqs : input.left = input.right
  · have zero : w 210 = 0 := equal.mpr eqs
    have resultZero : ∀ i < 16, result i = 0 := zeroFinite.mp ((sum_zero_iff hp h mapping.selected).mp zero)
    have final : (w 98).val = 0 := by simpa [carry, carryColumn] using difference.2 resultZero
    have finalField : w 98 = 0 := by
      calc
        _ = ((w 98).val : ZMod p) := (ZMod.natCast_zmod_val _).symm
        _ = 0 := by rw [final, Nat.cast_zero]
    simp [eqs, response.1, flag, zero, finalField, ZMod.val_one]
  · have nonzero : w 210 ≠ 0 := fun zero => eqs (equal.mp zero)
    simp [eqs, response.1, flag, nonzero]

end Airbender.Bigint.Equality.Proofs
