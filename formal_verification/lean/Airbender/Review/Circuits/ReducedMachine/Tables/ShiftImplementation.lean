import Airbender.Review.Circuits.ReducedMachine.Tables.Native
import Airbender.Review.Helpers.Tables.SllLow
import Airbender.Review.Helpers.Tables.SrlHigh

namespace Airbender.ReducedMachine.NativeFixed
open Verification

/-- Actual ID-37 key packs a 16-bit limb, five-bit amount and direction.
    The native right half returns high then low, opposite the split SRL-high table. -/
def shiftOutputs (key : Nat) : Vector Nat 2 :=
  if key < 2097152 then #v[sllHighOutput key,sllLowHighOutput key]
  else #v[srlLowOutput (key - 2097152),srlHighLowOutput (key - 2097152)]

end Airbender.ReducedMachine.NativeFixed
