import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn6Part2
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native6Part3 native6Rest3 native6Split3 from native6Rest2 at 1518
split_imported_blocks ordinary6Part3 ordinary6Rest3 ordinary6Split3 from ordinary6Rest2 at 1518
/-- Equality of one bounded slice of the independently imported data. -/
theorem common6Part3 : native6Part3 = ordinary6Part3 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge6Part3
    (backEqual : ∀ n, getFromBlocks native6Rest3.toList n = getFromBlocks ordinary6Rest3.toList n)
    (n : Nat) : getFromBlocks native6Rest2.toList n = getFromBlocks ordinary6Rest2.toList n := by
  exact split_blocks_agree native6Rest2 ordinary6Rest2 native6Part3 ordinary6Part3
    native6Rest3 ordinary6Rest3 native6Split3 ordinary6Split3 common6Part3 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
