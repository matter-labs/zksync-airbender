import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn7Part6
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native7Part7 native7Rest7 native7Split7 from native7Rest6 at 1542
split_imported_blocks ordinary7Part7 ordinary7Rest7 ordinary7Split7 from ordinary7Rest6 at 1542
/-- Equality of one bounded slice of the independently imported data. -/
theorem common7Part7 : native7Part7 = ordinary7Part7 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge7Part7
    (backEqual : ∀ n, getFromBlocks native7Rest7.toList n = getFromBlocks ordinary7Rest7.toList n)
    (n : Nat) : getFromBlocks native7Rest6.toList n = getFromBlocks ordinary7Rest6.toList n := by
  exact split_blocks_agree native7Rest6 ordinary7Rest6 native7Part7 ordinary7Part7
    native7Rest7 ordinary7Rest7 native7Split7 ordinary7Split7 common7Part7 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
