import Airbender.Proofs.ReducedMachine.NativeShiftBoundMath

namespace Airbender.ReducedMachine.NativeShiftNaturalProofs
open Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Right-shift halves occupy complementary residue positions below16bits. -/
theorem right_small_parts (lo hi amount block : Nat) (shape : block * 2 ^ amount = 65536)
    (low : lo < 65536) (high : hi < 65536) :
    lo / 2 ^ amount + (hi * 65536 / 2 ^ amount) % 65536 < 65536 ∧ hi / 2 ^ amount < block := by
  have positive : 0 < 2 ^ amount := Nat.pow_pos (by decide)
  have dv : hi * 65536 / 2 ^ amount = hi * block := by
    rw [← shape,← Nat.mul_assoc,Nat.mul_div_cancel _ positive]
  have md : (hi * block) % 65536 = (hi % 2 ^ amount) * block := by
    rw [← shape,Nat.mul_comm block (2 ^ amount)]
    exact Nat.mul_mod_mul_right _ _ _
  have gap := gap_sum lo hi (2 ^ amount) block positive
    (by simpa only [Nat.mul_comm,shape] using low)
  have upper : hi / 2 ^ amount < block :=
    (Nat.div_lt_iff_lt_mul positive).2 (by simpa only [shape] using high)
  refine ⟨?_,upper⟩
  rw [dv,md,Nat.add_comm]
  simpa only [Nat.mul_comm,shape] using gap

theorem right_small (lo hi amount block : Nat) (shape : block * 2 ^ amount = 65536)
    (low : lo < 65536) (high : hi < 65536) :
    assembledLow .right lo hi amount < 65536 ∧ assembledHigh .right lo hi amount < 65536 := by
  have parts := right_small_parts lo hi amount block shape low high
  have upper := lt_of_le_of_lt (Nat.div_le_self hi (2 ^ amount)) high
  simpa [assembledLow,assembledHigh,ShiftMode.filler] using And.intro parts.1 upper

/-- Above16bits the low input vanishes and the high contribution becomes a quotient. -/
theorem right_large_parts (lo hi amount factor : Nat) (shape : 2 ^ amount = 65536 * factor)
    (low : lo < 65536) (high : hi < 65536) :
    lo / 2 ^ amount = 0 ∧ hi / 2 ^ amount = 0 ∧
      (hi * 65536 / 2 ^ amount) % 65536 = hi / factor := by
  have positive : 0 < 2 ^ amount := Nat.pow_pos (by decide)
  have factorPos : 0 < factor := by omega
  have large : 65536 ≤ 2 ^ amount := by omega
  have dv : hi * 65536 / 2 ^ amount = hi / factor := by
    rw [shape,Nat.mul_comm 65536 factor]
    exact Nat.mul_div_mul_right _ _ (by decide)
  exact ⟨Nat.div_eq_of_lt (by omega),Nat.div_eq_of_lt (by omega),by
    rw [dv,Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) high)]⟩

theorem right_large (lo hi amount factor : Nat) (shape : 2 ^ amount = 65536 * factor)
    (low : lo < 65536) (high : hi < 65536) :
    assembledLow .right lo hi amount < 65536 ∧ assembledHigh .right lo hi amount < 65536 := by
  obtain ⟨lower,upper,part⟩ := right_large_parts lo hi amount factor shape low high
  have bound := lt_of_le_of_lt (Nat.div_le_self hi factor) high
  simpa [assembledLow,assembledHigh,ShiftMode.filler,lower,upper,part] using
    And.intro bound (by decide : 0 < 65536)

end Airbender.ReducedMachine.NativeShiftNaturalProofs
