import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn6Part6
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native6Part7 native6Rest7 native6Split7 from native6Rest6 at 1518
split_imported_blocks ordinary6Part7 ordinary6Rest7 ordinary6Split7 from ordinary6Rest6 at 1518
/-- Equality of one bounded slice of the independently imported data. -/
theorem common6Part7 : native6Part7 = ordinary6Part7 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge6Part7
    (backEqual : ∀ n, getFromBlocks native6Rest7.toList n = getFromBlocks ordinary6Rest7.toList n)
    (n : Nat) : getFromBlocks native6Rest6.toList n = getFromBlocks ordinary6Rest6.toList n := by
  exact split_blocks_agree native6Rest6 ordinary6Rest6 native6Part7 ordinary6Part7
    native6Rest7 ordinary6Rest7 native6Split7 ordinary6Split7 common6Part7 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
