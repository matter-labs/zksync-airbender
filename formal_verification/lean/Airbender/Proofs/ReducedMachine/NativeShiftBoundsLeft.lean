import Airbender.Proofs.ReducedMachine.NativeShiftBoundMath

namespace Airbender.ReducedMachine.NativeShiftNaturalProofs
open Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Exact native left-shift assembly stays in16bit limbs for a bounded low read. -/
theorem left_bounds (lo hi : Nat) (amount : Fin 32)
    (low : lo < 65536) (_high : hi < 65536) :
    assembledLow .left lo hi amount.val < 65536 ∧ assembledHigh .left lo hi amount.val < 65536 := by
  fin_cases amount
  · exact left_small lo hi 0 65536 (by decide) (by decide +kernel) low
  · exact left_small lo hi 1 32768 (by decide) (by decide +kernel) low
  · exact left_small lo hi 2 16384 (by decide) (by decide +kernel) low
  · exact left_small lo hi 3 8192 (by decide) (by decide +kernel) low
  · exact left_small lo hi 4 4096 (by decide) (by decide +kernel) low
  · exact left_small lo hi 5 2048 (by decide) (by decide +kernel) low
  · exact left_small lo hi 6 1024 (by decide) (by decide +kernel) low
  · exact left_small lo hi 7 512 (by decide) (by decide +kernel) low
  · exact left_small lo hi 8 256 (by decide) (by decide +kernel) low
  · exact left_small lo hi 9 128 (by decide) (by decide +kernel) low
  · exact left_small lo hi 10 64 (by decide) (by decide +kernel) low
  · exact left_small lo hi 11 32 (by decide) (by decide +kernel) low
  · exact left_small lo hi 12 16 (by decide) (by decide +kernel) low
  · exact left_small lo hi 13 8 (by decide) (by decide +kernel) low
  · exact left_small lo hi 14 4 (by decide) (by decide +kernel) low
  · exact left_small lo hi 15 2 (by decide) (by decide +kernel) low
  · exact left_small lo hi 16 1 (by decide) (by decide +kernel) low
  · exact left_large lo hi 17 2 (by decide +kernel)
  · exact left_large lo hi 18 4 (by decide +kernel)
  · exact left_large lo hi 19 8 (by decide +kernel)
  · exact left_large lo hi 20 16 (by decide +kernel)
  · exact left_large lo hi 21 32 (by decide +kernel)
  · exact left_large lo hi 22 64 (by decide +kernel)
  · exact left_large lo hi 23 128 (by decide +kernel)
  · exact left_large lo hi 24 256 (by decide +kernel)
  · exact left_large lo hi 25 512 (by decide +kernel)
  · exact left_large lo hi 26 1024 (by decide +kernel)
  · exact left_large lo hi 27 2048 (by decide +kernel)
  · exact left_large lo hi 28 4096 (by decide +kernel)
  · exact left_large lo hi 29 8192 (by decide +kernel)
  · exact left_large lo hi 30 16384 (by decide +kernel)
  · exact left_large lo hi 31 32768 (by decide +kernel)

end Airbender.ReducedMachine.NativeShiftNaturalProofs
