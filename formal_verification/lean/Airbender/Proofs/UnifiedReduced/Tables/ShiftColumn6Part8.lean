import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn6Part7
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native6Part8 native6Rest8 native6Split8 from native6Rest7 at 1517
split_imported_blocks ordinary6Part8 ordinary6Rest8 ordinary6Split8 from ordinary6Rest7 at 1517
/-- Equality of one bounded slice of the independently imported data. -/
theorem common6Part8 : native6Part8 = ordinary6Part8 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge6Part8
    (backEqual : ∀ n, getFromBlocks native6Rest8.toList n = getFromBlocks ordinary6Rest8.toList n)
    (n : Nat) : getFromBlocks native6Rest7.toList n = getFromBlocks ordinary6Rest7.toList n := by
  exact split_blocks_agree native6Rest7 ordinary6Rest7 native6Part8 ordinary6Part8
    native6Rest8 ordinary6Rest8 native6Split8 ordinary6Split8 common6Part8 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
