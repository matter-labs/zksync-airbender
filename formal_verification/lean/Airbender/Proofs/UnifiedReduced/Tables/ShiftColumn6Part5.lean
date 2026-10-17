import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn6Part4
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native6Part5 native6Rest5 native6Split5 from native6Rest4 at 1518
split_imported_blocks ordinary6Part5 ordinary6Rest5 ordinary6Split5 from ordinary6Rest4 at 1518
/-- Equality of one bounded slice of the independently imported data. -/
theorem common6Part5 : native6Part5 = ordinary6Part5 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge6Part5
    (backEqual : ∀ n, getFromBlocks native6Rest5.toList n = getFromBlocks ordinary6Rest5.toList n)
    (n : Nat) : getFromBlocks native6Rest4.toList n = getFromBlocks ordinary6Rest4.toList n := by
  exact split_blocks_agree native6Rest4 ordinary6Rest4 native6Part5 ordinary6Part5
    native6Rest5 ordinary6Rest5 native6Split5 ordinary6Split5 common6Part5 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
