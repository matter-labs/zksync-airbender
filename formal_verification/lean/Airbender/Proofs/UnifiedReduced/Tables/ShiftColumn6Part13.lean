import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn6Part12
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native6Part13 native6Rest13 native6Split13 from native6Rest12 at 1518
split_imported_blocks ordinary6Part13 ordinary6Rest13 ordinary6Split13 from ordinary6Rest12 at 1518
/-- Equality of one bounded slice of the independently imported data. -/
theorem common6Part13 : native6Part13 = ordinary6Part13 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge6Part13
    (backEqual : ∀ n, getFromBlocks native6Rest13.toList n = getFromBlocks ordinary6Rest13.toList n)
    (n : Nat) : getFromBlocks native6Rest12.toList n = getFromBlocks ordinary6Rest12.toList n := by
  exact split_blocks_agree native6Rest12 ordinary6Rest12 native6Part13 ordinary6Part13
    native6Rest13 ordinary6Rest13 native6Split13 ordinary6Split13 common6Part13 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
