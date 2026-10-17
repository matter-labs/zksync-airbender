import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn7Part1
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native7Part2 native7Rest2 native7Split2 from native7Rest1 at 1542
split_imported_blocks ordinary7Part2 ordinary7Rest2 ordinary7Split2 from ordinary7Rest1 at 1542
/-- Equality of one bounded slice of the independently imported data. -/
theorem common7Part2 : native7Part2 = ordinary7Part2 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge7Part2
    (backEqual : ∀ n, getFromBlocks native7Rest2.toList n = getFromBlocks ordinary7Rest2.toList n)
    (n : Nat) : getFromBlocks native7Rest1.toList n = getFromBlocks ordinary7Rest1.toList n := by
  exact split_blocks_agree native7Rest1 ordinary7Rest1 native7Part2 ordinary7Part2
    native7Rest2 ordinary7Rest2 native7Split2 ordinary7Split2 common7Part2 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
