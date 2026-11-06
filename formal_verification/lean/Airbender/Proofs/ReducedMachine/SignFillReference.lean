import Airbender.Review.Circuits.ReducedMachine.Row
import Airbender.Review.Circuits.ReducedMachine.Tables.Shift
import Lean.Elab.Tactic.Omega

namespace Airbender.ReducedMachine.SignFillReferenceProofs
open Native NativeFixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem logical (sign amount : Nat) (bound : sign ≤ 1) :
    signFillMask (sign + 4 * amount) = 0 := by
  have remainder : (sign + 4 * amount) % 4 = sign := by omega
  have inactive : sign ≠ 3 := by omega
  simp [signFillMask,remainder,inactive]

private theorem arithmetic (sign amount : Nat) (bound : sign ≤ 1) :
    signFillMask (2 + sign + 4 * amount) =
      if sign = 1 ∧ amount ≠ 0 then 4294967296 - 2 ^ (32 - amount) else 0 := by
  have remainder : (2 + sign + 4 * amount) % 4 = 2 + sign := by omega
  have quotient : (2 + sign + 4 * amount) / 4 = amount := by omega
  have active : 2 + sign = 3 ↔ sign = 1 := by omega
  simp [signFillMask,remainder,quotient,active]

/-- The native packed sign/control/amount key denotes the RV32 filler reference. -/
theorem reference (mode : ShiftMode) (high amount : Nat) (bound : high < 65536) :
    signFillMask (2 * (if mode = .arithmetic then 1 else 0) + high / 32768 + 4 * amount) =
      mode.filler high amount := by
  have signBound : high / 32768 ≤ 1 := by omega
  have negative : high / 32768 = 1 ↔ 32768 ≤ high := by omega
  cases mode with
  | left => simpa [ShiftMode.filler] using logical (high / 32768) amount signBound
  | right => simpa [ShiftMode.filler] using logical (high / 32768) amount signBound
  | arithmetic => simpa [ShiftMode.filler,negative] using arithmetic (high / 32768) amount signBound

end Airbender.ReducedMachine.SignFillReferenceProofs
