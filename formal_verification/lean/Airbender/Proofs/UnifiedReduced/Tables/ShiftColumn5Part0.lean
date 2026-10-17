import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ShiftColumn5
import Airbender.Review.Helpers.Tables.Shift.Column5
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native5Part0 native5Rest0 native5Split0 from nativeShiftColumn5 at 1533
split_imported_blocks ordinary5Part0 ordinary5Rest0 ordinary5Split0 from byteShiftColumn5 at 1533
/-- Equality of one bounded slice of the independently imported data. -/
theorem common5Part0 : native5Part0 = ordinary5Part0 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge5Part0
    (backEqual : ∀ n, getFromBlocks native5Rest0.toList n = getFromBlocks ordinary5Rest0.toList n)
    (n : Nat) : nativeShiftColumn5.get? n = byteShiftColumn5.get? n := by
  exact column_split_blocks_agree nativeShiftColumn5 byteShiftColumn5 native5Part0 ordinary5Part0
    native5Rest0 ordinary5Rest0 native5Split0 ordinary5Split0 common5Part0 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
