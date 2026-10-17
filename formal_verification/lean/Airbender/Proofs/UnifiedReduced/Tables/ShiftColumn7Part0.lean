import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ShiftColumn7
import Airbender.Review.Helpers.Tables.Shift.Column7
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native7Part0 native7Rest0 native7Split0 from nativeShiftColumn7 at 1541
split_imported_blocks ordinary7Part0 ordinary7Rest0 ordinary7Split0 from byteShiftColumn7 at 1541
/-- Equality of one bounded slice of the independently imported data. -/
theorem common7Part0 : native7Part0 = ordinary7Part0 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge7Part0
    (backEqual : ∀ n, getFromBlocks native7Rest0.toList n = getFromBlocks ordinary7Rest0.toList n)
    (n : Nat) : nativeShiftColumn7.get? n = byteShiftColumn7.get? n := by
  exact column_split_blocks_agree nativeShiftColumn7 byteShiftColumn7 native7Part0 ordinary7Part0
    native7Rest0 ordinary7Rest0 native7Split0 ordinary7Split0 common7Part0 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
