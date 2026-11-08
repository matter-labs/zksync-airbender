import Slop.ShiftBinop.Claims
import Slop.ShiftBinop.Completeness.Lookups
import Mathlib.Tactic.IntervalCases

namespace Tests.Binop
open Airbender
open Airbender.ShiftBinop

-- Complementary immediate/register bytes, sign extension, source/destination
-- aliasing and a PC limb carry. Every query and retained equation is satisfied.
private def instruction (operation : Fin 3) : Operation :=
  if operation.val = 0 then .xor else if operation.val = 1 then .or else .and

private def resultByte (operation : Fin 3) (byte : Nat) : Nat :=
  if operation.val = 0 then 255 - byte else if operation.val = 1 then 255 else byte

private def row (operation : Fin 3) (immediate : Bool) : Nat → ZMod babyBearModulus
  | 0 => 65532
  | 4 | 5 | 7 | 12 | 14 => 1
  | 6 => if immediate then 0 else 2
  | 8 | 9 | 35 | 52 | 53 => if immediate then 255 else 0
  | 10 | 64 | 73 | 82 | 91 => (instruction operation).tag
  | 15 => 4
  | 19 | 56 => 18
  | 20 | 65 => 205
  | 21 | 74 => 171
  | 22 | 83 => 128
  | 25 | 26 | 27 | 28 => if immediate then 0 else 255
  | 31 => resultByte operation 18 + 256 * resultByte operation 205
  | 32 => resultByte operation 171 + 256 * resultByte operation 128
  | 36 | 58 => resultByte operation 18
  | 37 | 67 => resultByte operation 205
  | 38 | 76 => resultByte operation 171
  | 39 | 85 => resultByte operation 128
  | 55 => 3
  | 57 | 66 | 75 | 84 => 255
  | _ => 0

private theorem satisfies (operation : Fin 3) (immediate : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (row operation immediate))
      importedConstraints := by
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  have equations : ∀ i : Fin (FlatOperation.constraints
      (importedConstraints (p := babyBearModulus))).length,
      ((FlatOperation.constraints importedConstraints).get i).eval
        (Verification.environment (row operation immediate)) = 0 := by
    intro i
    fin_cases i <;> fin_cases operation <;> cases immediate <;> decide
  have queries : ∀ i : Fin (FlatOperation.lookups
      (importedConstraints (p := babyBearModulus))).length,
      ((FlatOperation.lookups importedConstraints).get i).Contains
        (Verification.environment (row operation immediate)) := by
    intro i
    fin_cases i
    · exact Verification.range16_contains (by fin_cases operation <;> cases immediate <;> decide)
    · exact Verification.range16_contains (by fin_cases operation <;> cases immediate <;> decide)
    · exact Proofs.sign_query_of_columns (by fin_cases operation <;> cases immediate <;> decide +kernel)
    · exact Proofs.query_of_columns 0 (by fin_cases operation <;> cases immediate <;> decide +kernel)
    · exact Proofs.query_of_columns 1 (by fin_cases operation <;> cases immediate <;> decide +kernel)
    · exact Proofs.query_of_columns 2 (by fin_cases operation <;> cases immediate <;> decide +kernel)
    · exact Proofs.query_of_columns 3 (by fin_cases operation <;> cases immediate <;> decide +kernel)
  constructor
  · intro c hc
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hc
    exact equations i
  · intro q hq
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hq
    exact queries i

end Tests.Binop
