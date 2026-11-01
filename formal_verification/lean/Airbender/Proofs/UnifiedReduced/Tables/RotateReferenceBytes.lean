import Airbender.Review.Helpers.Tables.Range
import Airbender.Proofs.Tables.FiniteGridChecks

namespace Airbender.UnifiedReduced.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

def nativeRotations : Vector Nat 4 := #v[16, 12, 8, 7]
def referenceRotatedByte (mode lane : Fin 4) (value : Nat) : Nat :=
  ((BitVec.ofNat 32 value).rotateRight nativeRotations[mode]).toNat / 256 ^ lane.val % 256

def finiteRotatedByte (mode lane : Fin 4) (value : Nat) : Nat :=
  if mode.val = 0 then (if lane.val = 2 then value else 0)
  else if mode.val = 1 then
    (if lane.val = 2 then value % 16 * 16 else if lane.val = 3 then value / 16 else 0)
  else if mode.val = 2 then (if lane.val = 3 then value else 0)
  else if lane.val = 0 then value / 128 else if lane.val = 3 then value % 128 * 2 else 0

def rotationByteCheck : Bool := Verification.FiniteGridChecks.check 4 4 256
  (fun mode lane value => referenceRotatedByte mode lane value.val)
  (fun mode lane value => finiteRotatedByte mode lane value.val)

theorem rotationByteChecked : rotationByteCheck = true := by decide +kernel

/-- The complete kernel result derives the original reference equation. -/
theorem rotated_byte_reference (mode lane : Fin 4) (value : Fin 256) :
    referenceRotatedByte mode lane value.val = finiteRotatedByte mode lane value.val :=
  Verification.FiniteGridChecks.check_sound 4 4 256 _ _ rotationByteChecked mode lane value

end Airbender.UnifiedReduced.Setup.Proofs
