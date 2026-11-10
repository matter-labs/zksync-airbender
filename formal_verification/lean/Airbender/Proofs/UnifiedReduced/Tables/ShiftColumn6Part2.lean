import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn6Part1
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native6Part2 native6Rest2 native6Split2 from native6Rest1 at 1518
split_imported_blocks ordinary6Part2 ordinary6Rest2 ordinary6Split2 from ordinary6Rest1 at 1518
/-- Equality of one bounded slice of the independently imported data. -/
theorem common6Part2 : native6Part2 = ordinary6Part2 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge6Part2
    (backEqual : ∀ n, getFromBlocks native6Rest2.toList n = getFromBlocks ordinary6Rest2.toList n)
    (n : Nat) : getFromBlocks native6Rest1.toList n = getFromBlocks ordinary6Rest1.toList n := by
  exact split_blocks_agree native6Rest1 ordinary6Rest1 native6Part2 ordinary6Part2
    native6Rest2 ordinary6Rest2 native6Split2 ordinary6Split2 common6Part2 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
