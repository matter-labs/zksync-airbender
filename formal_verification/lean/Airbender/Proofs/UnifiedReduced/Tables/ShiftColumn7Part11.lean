import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn7Part10
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native7Part11 native7Rest11 native7Split11 from native7Rest10 at 1542
split_imported_blocks ordinary7Part11 ordinary7Rest11 ordinary7Split11 from ordinary7Rest10 at 1542
/-- Equality of one bounded slice of the independently imported data. -/
theorem common7Part11 : native7Part11 = ordinary7Part11 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge7Part11
    (backEqual : ∀ n, getFromBlocks native7Rest11.toList n = getFromBlocks ordinary7Rest11.toList n)
    (n : Nat) : getFromBlocks native7Rest10.toList n = getFromBlocks ordinary7Rest10.toList n := by
  exact split_blocks_agree native7Rest10 ordinary7Rest10 native7Part11 ordinary7Part11
    native7Rest11 ordinary7Rest11 native7Split11 ordinary7Split11 common7Part11 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
