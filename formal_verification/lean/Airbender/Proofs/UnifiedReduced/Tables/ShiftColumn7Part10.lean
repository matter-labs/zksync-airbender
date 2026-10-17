import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn7Part9
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native7Part10 native7Rest10 native7Split10 from native7Rest9 at 1541
split_imported_blocks ordinary7Part10 ordinary7Rest10 ordinary7Split10 from ordinary7Rest9 at 1541
/-- Equality of one bounded slice of the independently imported data. -/
theorem common7Part10 : native7Part10 = ordinary7Part10 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge7Part10
    (backEqual : ∀ n, getFromBlocks native7Rest10.toList n = getFromBlocks ordinary7Rest10.toList n)
    (n : Nat) : getFromBlocks native7Rest9.toList n = getFromBlocks ordinary7Rest9.toList n := by
  exact split_blocks_agree native7Rest9 ordinary7Rest9 native7Part10 ordinary7Part10
    native7Rest10 ordinary7Rest10 native7Split10 ordinary7Split10 common7Part10 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
