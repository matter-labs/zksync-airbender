import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn7Part7
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native7Part8 native7Rest8 native7Split8 from native7Rest7 at 1542
split_imported_blocks ordinary7Part8 ordinary7Rest8 ordinary7Split8 from ordinary7Rest7 at 1542
/-- Equality of one bounded slice of the independently imported data. -/
theorem common7Part8 : native7Part8 = ordinary7Part8 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge7Part8
    (backEqual : ∀ n, getFromBlocks native7Rest8.toList n = getFromBlocks ordinary7Rest8.toList n)
    (n : Nat) : getFromBlocks native7Rest7.toList n = getFromBlocks ordinary7Rest7.toList n := by
  exact split_blocks_agree native7Rest7 ordinary7Rest7 native7Part8 ordinary7Part8
    native7Rest8 ordinary7Rest8 native7Split8 ordinary7Split8 common7Part8 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
