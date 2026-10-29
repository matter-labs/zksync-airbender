import Airbender.Proofs.Trace.Timestamps

namespace Airbender.Keccak.Split.Proofs
open Airbender.Trace
set_option warningAsError true

/-- A positive grouped read distance gives strict order without a separate
timestamp lookup for every port in the group. -/
theorem grouped_distance_order [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {initial previous : Timestamp} (ib : initial.Bounded)
    (pb : previous.Bounded) {distance : Nat}
    (positive : 0 < distance) (small : 4 * distance < timestampBase)
    {borrow : ZMod p} (bit : borrow * (borrow - 1) = 0)
    (low : (previous.lo : ZMod p) - (initial.lo : ZMod p) - 2 +
      ((4 * distance : Nat) : ZMod p) - (timestampBase : ZMod p) * borrow = 0)
    (high : (previous.hi : ZMod p) - (initial.hi : ZMod p) + borrow = 0) :
    previous.value < initial.value + 2 := by
  obtain ⟨carry, cb, equation⟩ := Arithmetic.boolean_nat bit
  rw [equation] at low high
  have lowCast : ((previous.lo + 4 * distance : Nat) : ZMod p) =
      ((initial.lo + 2 + timestampBase * carry : Nat) : ZMod p) := by
    push_cast
    simp only [Nat.cast_mul] at low
    linear_combination low
  have highCast : ((previous.hi + carry : Nat) : ZMod p) =
      (initial.hi : ZMod p) := by
    push_cast
    linear_combination high
  have lowNat : previous.lo + 4 * distance =
      initial.lo + 2 + timestampBase * carry := by
    apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p)
      (by have := pb.1; omega)
      (by
        have := ib.1
        rcases (show carry = 0 ∨ carry = 1 by omega) with rfl | rfl
        · simp only [mul_zero, add_zero]; omega
        · simp only [mul_one]; omega)
    exact lowCast
  have highNat : previous.hi + carry = initial.hi := by
    apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p)
      (by have := pb.2; omega) (by have := ib.2; omega)
    exact highCast
  have highScaled := congrArg (fun x : Nat => timestampBase * x) highNat
  simp only [mul_add] at highScaled
  simp only [Timestamp.value]
  omega

end Airbender.Keccak.Split.Proofs
