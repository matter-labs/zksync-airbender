import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn6Part5
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native6Part6 native6Rest6 native6Split6 from native6Rest5 at 1518
split_imported_blocks ordinary6Part6 ordinary6Rest6 ordinary6Split6 from ordinary6Rest5 at 1518
/-- Equality of one bounded slice of the independently imported data. -/
theorem common6Part6 : native6Part6 = ordinary6Part6 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge6Part6
    (backEqual : ∀ n, getFromBlocks native6Rest6.toList n = getFromBlocks ordinary6Rest6.toList n)
    (n : Nat) : getFromBlocks native6Rest5.toList n = getFromBlocks ordinary6Rest5.toList n := by
  exact split_blocks_agree native6Rest5 ordinary6Rest5 native6Part6 ordinary6Part6
    native6Rest6 ordinary6Rest6 native6Split6 ordinary6Split6 common6Part6 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
