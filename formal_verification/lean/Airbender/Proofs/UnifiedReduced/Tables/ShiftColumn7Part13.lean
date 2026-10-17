import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn7Part12
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native7Part13 native7Rest13 native7Split13 from native7Rest12 at 1542
split_imported_blocks ordinary7Part13 ordinary7Rest13 ordinary7Split13 from ordinary7Rest12 at 1542
/-- Equality of one bounded slice of the independently imported data. -/
theorem common7Part13 : native7Part13 = ordinary7Part13 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge7Part13
    (backEqual : ∀ n, getFromBlocks native7Rest13.toList n = getFromBlocks ordinary7Rest13.toList n)
    (n : Nat) : getFromBlocks native7Rest12.toList n = getFromBlocks ordinary7Rest12.toList n := by
  exact split_blocks_agree native7Rest12 ordinary7Rest12 native7Part13 ordinary7Part13
    native7Rest13 ordinary7Rest13 native7Split13 ordinary7Split13 common7Part13 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
