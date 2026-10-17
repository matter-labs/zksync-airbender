import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn7Part5
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native7Part6 native7Rest6 native7Split6 from native7Rest5 at 1542
split_imported_blocks ordinary7Part6 ordinary7Rest6 ordinary7Split6 from ordinary7Rest5 at 1542
/-- Equality of one bounded slice of the independently imported data. -/
theorem common7Part6 : native7Part6 = ordinary7Part6 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge7Part6
    (backEqual : ∀ n, getFromBlocks native7Rest6.toList n = getFromBlocks ordinary7Rest6.toList n)
    (n : Nat) : getFromBlocks native7Rest5.toList n = getFromBlocks ordinary7Rest5.toList n := by
  exact split_blocks_agree native7Rest5 ordinary7Rest5 native7Part6 ordinary7Part6
    native7Rest6 ordinary7Rest6 native7Split6 ordinary7Split6 common7Part6 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
