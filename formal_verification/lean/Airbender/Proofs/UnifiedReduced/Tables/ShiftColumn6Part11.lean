import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn6Part10
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native6Part11 native6Rest11 native6Split11 from native6Rest10 at 1518
split_imported_blocks ordinary6Part11 ordinary6Rest11 ordinary6Split11 from ordinary6Rest10 at 1518
/-- Equality of one bounded slice of the independently imported data. -/
theorem common6Part11 : native6Part11 = ordinary6Part11 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge6Part11
    (backEqual : ∀ n, getFromBlocks native6Rest11.toList n = getFromBlocks ordinary6Rest11.toList n)
    (n : Nat) : getFromBlocks native6Rest10.toList n = getFromBlocks ordinary6Rest10.toList n := by
  exact split_blocks_agree native6Rest10 ordinary6Rest10 native6Part11 ordinary6Part11
    native6Rest11 ordinary6Rest11 native6Split11 ordinary6Split11 common6Part11 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
