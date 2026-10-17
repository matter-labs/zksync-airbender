import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.ShiftColumn6
import Airbender.Review.Helpers.Tables.Shift.Column6
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native6Part0 native6Rest0 native6Split0 from nativeShiftColumn6 at 1517
split_imported_blocks ordinary6Part0 ordinary6Rest0 ordinary6Split0 from byteShiftColumn6 at 1517
/-- Equality of one bounded slice of the independently imported data. -/
theorem common6Part0 : native6Part0 = ordinary6Part0 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge6Part0
    (backEqual : ∀ n, getFromBlocks native6Rest0.toList n = getFromBlocks ordinary6Rest0.toList n)
    (n : Nat) : nativeShiftColumn6.get? n = byteShiftColumn6.get? n := by
  exact column_split_blocks_agree nativeShiftColumn6 byteShiftColumn6 native6Part0 ordinary6Part0
    native6Rest0 ordinary6Rest0 native6Split0 ordinary6Split0 common6Part0 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
