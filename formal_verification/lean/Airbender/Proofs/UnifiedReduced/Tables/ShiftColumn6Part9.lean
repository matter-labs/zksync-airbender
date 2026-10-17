import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn6Part8
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native6Part9 native6Rest9 native6Split9 from native6Rest8 at 1518
split_imported_blocks ordinary6Part9 ordinary6Rest9 ordinary6Split9 from ordinary6Rest8 at 1518
/-- Equality of one bounded slice of the independently imported data. -/
theorem common6Part9 : native6Part9 = ordinary6Part9 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge6Part9
    (backEqual : ∀ n, getFromBlocks native6Rest9.toList n = getFromBlocks ordinary6Rest9.toList n)
    (n : Nat) : getFromBlocks native6Rest8.toList n = getFromBlocks ordinary6Rest8.toList n := by
  exact split_blocks_agree native6Rest8 ordinary6Rest8 native6Part9 ordinary6Part9
    native6Rest9 ordinary6Rest9 native6Split9 ordinary6Split9 common6Part9 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
