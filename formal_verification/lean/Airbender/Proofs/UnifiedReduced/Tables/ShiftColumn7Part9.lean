import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn7Part8
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native7Part9 native7Rest9 native7Split9 from native7Rest8 at 1542
split_imported_blocks ordinary7Part9 ordinary7Rest9 ordinary7Split9 from ordinary7Rest8 at 1542
/-- Equality of one bounded slice of the independently imported data. -/
theorem common7Part9 : native7Part9 = ordinary7Part9 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge7Part9
    (backEqual : ∀ n, getFromBlocks native7Rest9.toList n = getFromBlocks ordinary7Rest9.toList n)
    (n : Nat) : getFromBlocks native7Rest8.toList n = getFromBlocks ordinary7Rest8.toList n := by
  exact split_blocks_agree native7Rest8 ordinary7Rest8 native7Part9 ordinary7Part9
    native7Rest9 ordinary7Rest9 native7Split9 ordinary7Split9 common7Part9 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
