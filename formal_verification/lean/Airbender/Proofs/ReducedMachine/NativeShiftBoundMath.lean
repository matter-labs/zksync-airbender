import Airbender.Proofs.ReducedMachine.NativeShiftNatural

namespace Airbender.ReducedMachine.NativeShiftNaturalProofs
open Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- A quotient fits in the gap below the next multiple of the stride. -/
theorem gap_sum (x y block stride : Nat) (blockPos : 0 < block) (source : x < block * stride) :
    (y % block) * stride + x / block < block * stride := by
  have quotient : x / block < stride :=
    (Nat.div_lt_iff_lt_mul blockPos).2 (by simpa only [Nat.mul_comm] using source)
  have rem : y % block + 1 ≤ block := by have := Nat.mod_lt y blockPos; omega
  calc
    (y % block) * stride + x / block < (y % block) * stride + stride := Nat.add_lt_add_left quotient _
    _ = (y % block + 1) * stride := by ring
    _ ≤ block * stride := Nat.mul_le_mul_right _ rem

/-- Small left shifts share a symbolic stride; no large-coefficient search is needed. -/
theorem left_small (lo hi amount block : Nat) (blockPos : 0 < block)
    (shape : block * 2 ^ amount = 65536) (low : lo < 65536) :
    assembledLow .left lo hi amount < 65536 ∧ assembledHigh .left lo hi amount < 65536 := by
  change (lo * 2 ^ amount) % 65536 < 65536 ∧
    (hi * 2 ^ amount) % 65536 + (lo * 2 ^ amount / 65536) % 65536 < 65536
  have positive : 0 < 2 ^ amount := Nat.pow_pos (by decide)
  have md : (hi * 2 ^ amount) % 65536 = (hi % block) * 2 ^ amount := by
    rw [← shape]
    exact Nat.mul_mod_mul_right _ _ _
  have dv : lo * 2 ^ amount / 65536 = lo / block := by
    rw [← shape]
    exact Nat.mul_div_mul_right _ _ positive
  have quo : lo / block < 65536 := lt_of_le_of_lt (Nat.div_le_self _ _) low
  refine ⟨Nat.mod_lt _ (by decide),?_⟩
  rw [md,dv,Nat.mod_eq_of_lt quo]
  have result := gap_sum lo hi block (2 ^ amount) blockPos (by simpa only [shape] using low)
  simpa only [shape] using result

/-- Large left shifts have no high-input contribution in the retained word. -/
theorem left_large (lo hi amount factor : Nat) (shape : 2 ^ amount = 65536 * factor) :
    assembledLow .left lo hi amount < 65536 ∧ assembledHigh .left lo hi amount < 65536 := by
  have zero (x : Nat) : (x * 2 ^ amount) % 65536 = 0 := by
    rw [shape,Nat.mul_left_comm x 65536,Nat.mul_mod_right]
  have carry : (lo * 2 ^ amount / 65536) % 65536 = (lo * factor) % 65536 := by
    rw [shape,Nat.mul_left_comm lo 65536,Nat.mul_div_cancel_left _ (by decide)]
  change (lo * 2 ^ amount) % 65536 < 65536 ∧
    (hi * 2 ^ amount) % 65536 + (lo * 2 ^ amount / 65536) % 65536 < 65536
  rw [zero lo,zero hi,carry,zero_add]
  exact ⟨by decide,Nat.mod_lt _ (by decide)⟩

end Airbender.ReducedMachine.NativeShiftNaturalProofs
