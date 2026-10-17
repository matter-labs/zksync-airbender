import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn6Part9
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native6Part10 native6Rest10 native6Split10 from native6Rest9 at 1518
split_imported_blocks ordinary6Part10 ordinary6Rest10 ordinary6Split10 from ordinary6Rest9 at 1518
/-- Equality of one bounded slice of the independently imported data. -/
theorem common6Part10 : native6Part10 = ordinary6Part10 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge6Part10
    (backEqual : ∀ n, getFromBlocks native6Rest10.toList n = getFromBlocks ordinary6Rest10.toList n)
    (n : Nat) : getFromBlocks native6Rest9.toList n = getFromBlocks ordinary6Rest9.toList n := by
  exact split_blocks_agree native6Rest9 ordinary6Rest9 native6Part10 ordinary6Part10
    native6Rest10 ordinary6Rest10 native6Split10 ordinary6Split10 common6Part10 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
