import Airbender.Proofs.ReducedMachine.NativeShiftArithmeticMath
import Airbender.Proofs.ReducedMachine.NativeShiftBoundsRight

namespace Airbender.ReducedMachine.NativeShiftNaturalProofs
open Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem arithmetic_bounds (lo hi : Nat) (amount : Fin 32)
    (low : lo < 65536) (high : hi < 65536) :
    assembledLow .arithmetic lo hi amount.val < 65536 ∧ assembledHigh .arithmetic lo hi amount.val < 65536 := by
  by_cases sign : hi < 32768
  · have fill : ShiftMode.arithmetic.filler hi amount.val = 0 := by
      simp [ShiftMode.filler,show ¬ 32768 ≤ hi by omega]
    have right := right_bounds lo hi amount low high
    simpa [assembledLow,assembledHigh,ShiftMode.filler,show ¬ 32768 ≤ hi by omega] using right
  have negative : 32768 ≤ hi := by omega
  fin_cases amount
  · simpa [assembledLow,assembledHigh,ShiftMode.filler] using right_bounds lo hi ⟨0,by decide⟩ low high
  · apply arithmetic_small lo hi 1 32768 (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_small lo hi 2 16384 (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_small lo hi 3 8192 (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_small lo hi 4 4096 (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_small lo hi 5 2048 (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_small lo hi 6 1024 (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_small lo hi 7 512 (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_small lo hi 8 256 (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_small lo hi 9 128 (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_small lo hi 10 64 (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_small lo hi 11 32 (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_small lo hi 12 16 (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_small lo hi 13 8 (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_small lo hi 14 4 (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_small lo hi 15 2 (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_small lo hi 16 1 (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_large lo hi 17 2 32768 (by decide +kernel) (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_large lo hi 18 4 16384 (by decide +kernel) (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_large lo hi 19 8 8192 (by decide +kernel) (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_large lo hi 20 16 4096 (by decide +kernel) (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_large lo hi 21 32 2048 (by decide +kernel) (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_large lo hi 22 64 1024 (by decide +kernel) (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_large lo hi 23 128 512 (by decide +kernel) (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_large lo hi 24 256 256 (by decide +kernel) (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_large lo hi 25 512 128 (by decide +kernel) (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_large lo hi 26 1024 64 (by decide +kernel) (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_large lo hi 27 2048 32 (by decide +kernel) (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_large lo hi 28 4096 16 (by decide +kernel) (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_large lo hi 29 8192 8 (by decide +kernel) (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_large lo hi 30 16384 4 (by decide +kernel) (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel
  · apply arithmetic_large lo hi 31 32768 2 (by decide +kernel) (by decide +kernel) low high
    rw [ShiftMode.filler,if_pos ⟨rfl,negative,by decide⟩]
    decide +kernel

end Airbender.ReducedMachine.NativeShiftNaturalProofs
