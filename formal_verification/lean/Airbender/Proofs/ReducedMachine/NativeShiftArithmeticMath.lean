import Airbender.Proofs.ReducedMachine.NativeShiftRightMath

namespace Airbender.ReducedMachine.NativeShiftNaturalProofs
open Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem arithmetic_small (lo hi amount block : Nat) (shape : block * 2 ^ amount = 65536)
    (low : lo < 65536) (high : hi < 65536)
    (fill : ShiftMode.arithmetic.filler hi amount % 65536 = 0 ∧
      ShiftMode.arithmetic.filler hi amount / 65536 = 65536 - block) :
    assembledLow .arithmetic lo hi amount < 65536 ∧ assembledHigh .arithmetic lo hi amount < 65536 := by
  have parts := right_small_parts lo hi amount block shape low high
  have positive : 0 < 2 ^ amount := Nat.pow_pos (by decide)
  have blockBound : block ≤ 65536 := by
    calc
      block = block * 1 := by ring
      _ ≤ block * 2 ^ amount := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt positive)
      _ = 65536 := shape
  change lo / 2 ^ amount + (hi * 65536 / 2 ^ amount) % 65536 + _ < 65536 ∧
    hi / 2 ^ amount + _ < 65536
  rw [fill.1,fill.2,add_zero]
  exact ⟨parts.1,by omega⟩

theorem arithmetic_large (lo hi amount factor block : Nat)
    (shape : 2 ^ amount = 65536 * factor) (split : block * factor = 65536)
    (low : lo < 65536) (high : hi < 65536)
    (fill : ShiftMode.arithmetic.filler hi amount % 65536 = 65536 - block ∧
      ShiftMode.arithmetic.filler hi amount / 65536 = 65535) :
    assembledLow .arithmetic lo hi amount < 65536 ∧ assembledHigh .arithmetic lo hi amount < 65536 := by
  obtain ⟨lower,upper,part⟩ := right_large_parts lo hi amount factor shape low high
  have positive : 0 < 2 ^ amount := Nat.pow_pos (by decide)
  have factorPos : 0 < factor := by omega
  have quotient : hi / factor < block :=
    (Nat.div_lt_iff_lt_mul factorPos).2 (by simpa only [split] using high)
  have blockBound : block ≤ 65536 := by
    calc
      block = block * 1 := by ring
      _ ≤ block * factor := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt factorPos)
      _ = 65536 := split
  change lo / 2 ^ amount + (hi * 65536 / 2 ^ amount) % 65536 + _ < 65536 ∧
    hi / 2 ^ amount + _ < 65536
  rw [lower,upper,part,fill.1,fill.2,zero_add,zero_add]
  exact ⟨by omega,by decide⟩

end Airbender.ReducedMachine.NativeShiftNaturalProofs
