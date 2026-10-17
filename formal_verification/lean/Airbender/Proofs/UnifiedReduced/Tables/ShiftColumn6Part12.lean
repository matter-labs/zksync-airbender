import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn6Part11
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native6Part12 native6Rest12 native6Split12 from native6Rest11 at 1518
split_imported_blocks ordinary6Part12 ordinary6Rest12 ordinary6Split12 from ordinary6Rest11 at 1518
/-- Equality of one bounded slice of the independently imported data. -/
theorem common6Part12 : native6Part12 = ordinary6Part12 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge6Part12
    (backEqual : ∀ n, getFromBlocks native6Rest12.toList n = getFromBlocks ordinary6Rest12.toList n)
    (n : Nat) : getFromBlocks native6Rest11.toList n = getFromBlocks ordinary6Rest11.toList n := by
  exact split_blocks_agree native6Rest11 ordinary6Rest11 native6Part12 ordinary6Part12
    native6Rest12 ordinary6Rest12 native6Split12 ordinary6Split12 common6Part12 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
