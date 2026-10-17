import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn7Part2
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native7Part3 native7Rest3 native7Split3 from native7Rest2 at 1542
split_imported_blocks ordinary7Part3 ordinary7Rest3 ordinary7Split3 from ordinary7Rest2 at 1542
/-- Equality of one bounded slice of the independently imported data. -/
theorem common7Part3 : native7Part3 = ordinary7Part3 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge7Part3
    (backEqual : ∀ n, getFromBlocks native7Rest3.toList n = getFromBlocks ordinary7Rest3.toList n)
    (n : Nat) : getFromBlocks native7Rest2.toList n = getFromBlocks ordinary7Rest2.toList n := by
  exact split_blocks_agree native7Rest2 ordinary7Rest2 native7Part3 ordinary7Part3
    native7Rest3 ordinary7Rest3 native7Split3 ordinary7Split3 common7Part3 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
