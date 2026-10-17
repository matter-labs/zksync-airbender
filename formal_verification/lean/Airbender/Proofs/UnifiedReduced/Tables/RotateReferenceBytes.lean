import Airbender.Review.Helpers.Tables.Range
import Mathlib.Tactic.FinCases

namespace Airbender.UnifiedReduced.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

def nativeRotations : Vector Nat 4 := #v[16, 12, 8, 7]
def referenceRotatedByte (mode lane : Fin 4) (value : Nat) : Nat :=
  ((BitVec.ofNat 32 value).rotateRight nativeRotations[mode]).toNat / 256 ^ lane.val % 256

def finiteRotatedByte (mode lane : Fin 4) (value : Nat) : Nat :=
  if mode.val = 0 then (if lane.val = 2 then value else 0)
  else if mode.val = 1 then
    (if lane.val = 2 then value % 16 * 16 else if lane.val = 3 then value / 16 else 0)
  else if mode.val = 2 then (if lane.val = 3 then value else 0)
  else if lane.val = 0 then value / 128 else if lane.val = 3 then value % 128 * 2 else 0

/-- The original 32-bit rotation reference on every possible byte value. -/
theorem rotated_byte_reference (mode lane : Fin 4) (value : Fin 256) :
    referenceRotatedByte mode lane value.val = finiteRotatedByte mode lane value.val := by
  fin_cases mode <;> fin_cases lane
  all_goals revert value; decide +kernel

end Airbender.UnifiedReduced.Setup.Proofs
