import Slop.Bigint.MultiplicationColumns
import Slop.Bigint.MultiplicationFields

namespace Airbender.Bigint.Multiplication.Proofs
open Arithmetic
open scoped BigOperators
set_option warningAsError true
set_option maxHeartbeats 2000000

def leftSource (w : Nat → ZMod p) (i : Fin 16) : Nat := (w Variables.leftLimbs[i]).val
def rightSource (w : Nat → ZMod p) (i : Fin 16) : Nat := (w Variables.rightLimbs[i]).val

def carryValue (w : Nat → ZMod p) (i : Nat) : Nat :=
  if first : i = 0 then 0
  else if small : i < 32 then (carry w ⟨i - 1, by omega⟩).val else 0

theorem incoming_value (w : Nat → ZMod p) (i : Fin 32) :
    (incoming w i).val = carryValue w i.val := by
  have bound := i.isLt
  by_cases first : i.val = 0 <;> simp [incoming, carryValue, first, bound]

theorem outgoing_value (w : Nat → ZMod p) (i : Fin 32) :
    (outgoing w i).val = carryValue w (i.val + 1) := by
  by_cases last : i.val < 31
  · have bound : i.val + 1 < 32 := by omega
    simp [outgoing, carryValue, last, bound]
  · have bound : ¬ i.val + 1 < 32 := by omega
    simp [outgoing, carryValue, last, bound]

theorem carry_value_bound {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (i : Nat) : carryValue w i < 8192 := by
  unfold carryValue
  split_ifs
  · decide
  · exact carry_bounded hp h _
  · decide

/-- Lift the native byte columns separately. Lifting only a whole-product field
    equality would lose multiples of the characteristic. -/
theorem natural_columns {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (selected : w 62 = 1 ∨ w 63 = 1) :
    ∀ i : Fin 32, multiplicationColumn (leftSource w) (rightSource w) i.val + carryValue w i.val =
      (w (131 + i.val)).val + 65536 * carryValue w (i.val + 1) := by
  have sources : ∀ i, w Variables.leftLimbs[i] = (leftSource w i : ZMod babyBearModulus) ∧
      w Variables.rightLimbs[i] = (rightSource w i : ZMod babyBearModulus) := by
    intro i
    exact ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm⟩
  have gates := native_columns h sources (source_low_bytes (by decide) h)
  have inputBound := Bigint.Proofs.source_ranges (by decide) h
  have resultBound := product_ranges (by decide) h selected
  intro i
  have columnBound := multiplication_column_bound (a := leftSource w) (b := rightSource w)
    (fun j => (inputBound j).1) (fun j => (inputBound j).2) (column := i.val)
  have carryIn := carry_value_bound (by decide) h i.val
  have carryOut := carry_value_bound (by decide) h (i.val + 1)
  have limbBound := resultBound i
  have scaled := Nat.mul_le_mul_left 65536 (by omega : carryValue w (i.val + 1) ≤ 8191)
  have inCast : (carryValue w i.val : ZMod babyBearModulus) = incoming w i := by
    rw [← incoming_value, ZMod.natCast_zmod_val]
  have outCast : (carryValue w (i.val + 1) : ZMod babyBearModulus) = outgoing w i := by
    rw [← outgoing_value, ZMod.natCast_zmod_val]
  apply bounded_nat_eq (F := ZMod babyBearModulus) (p := babyBearModulus)
  · calc
      _ ≤ 534765600 + 8191 := Nat.add_le_add columnBound (Nat.le_sub_one_of_lt carryIn)
      _ < babyBearModulus := by decide
  · calc
      _ ≤ 65535 + 65536 * 8191 :=
        Nat.add_le_add (Nat.le_sub_one_of_lt limbBound) scaled
      _ < babyBearModulus := by decide
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val,
      inCast, outCast] using gates i

/-- Exact 512-bit product of the actual source-port limbs. Only native equations
    and the modeled setup are used; no product or carry premise is supplied. -/
theorem full_product {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (selected : w 62 = 1 ∨ w 63 = 1) :
    (∑ i : Fin 16, 65536 ^ i.val * leftSource w i) *
      (∑ i : Fin 16, 65536 ^ i.val * rightSource w i) =
      ∑ i : Fin 32, 65536 ^ i.val * (w (131 + i.val)).val := by
  have steps := natural_columns h selected
  have chain := carry_chain (radix := 65536) (length := 32)
    (left := multiplicationColumn (leftSource w) (rightSource w)) (right := fun _ => 0)
    (result := fun i => (w (131 + i)).val) (carry := carryValue w)
    (fun i bound => by simpa only [Nat.add_zero] using steps ⟨i, bound⟩)
  simp [carryValue, limbSum] at chain
  calc
    _ = ∑ i : Fin 32, 65536 ^ i.val * multiplicationColumn (leftSource w) (rightSource w) i.val :=
      (multiplication_columns (leftSource w) (rightSource w)).symm
    _ = limbSum 65536 32 (multiplicationColumn (leftSource w) (rightSource w)) :=
      Fin.sum_univ_eq_sum_range (fun i => 65536 ^ i * multiplicationColumn (leftSource w) (rightSource w) i) 32
    _ = limbSum 65536 32 (fun i => (w (131 + i)).val) := chain
    _ = _ := (Fin.sum_univ_eq_sum_range (fun i => 65536 ^ i * (w (131 + i)).val) 32).symm

end Airbender.Bigint.Multiplication.Proofs
