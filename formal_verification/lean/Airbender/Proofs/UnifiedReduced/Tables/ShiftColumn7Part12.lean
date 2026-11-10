import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn7Part11
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native7Part12 native7Rest12 native7Split12 from native7Rest11 at 1542
split_imported_blocks ordinary7Part12 ordinary7Rest12 ordinary7Split12 from ordinary7Rest11 at 1542
/-- Equality of one bounded slice of the independently imported data. -/
theorem common7Part12 : native7Part12 = ordinary7Part12 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge7Part12
    (backEqual : ∀ n, getFromBlocks native7Rest12.toList n = getFromBlocks ordinary7Rest12.toList n)
    (n : Nat) : getFromBlocks native7Rest11.toList n = getFromBlocks ordinary7Rest11.toList n := by
  exact split_blocks_agree native7Rest11 ordinary7Rest11 native7Part12 ordinary7Part12
    native7Rest12 ordinary7Rest12 native7Split12 ordinary7Split12 common7Part12 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
