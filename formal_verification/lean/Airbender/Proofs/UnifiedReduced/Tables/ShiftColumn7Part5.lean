import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn7Part4
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native7Part5 native7Rest5 native7Split5 from native7Rest4 at 1541
split_imported_blocks ordinary7Part5 ordinary7Rest5 ordinary7Split5 from ordinary7Rest4 at 1541
/-- Equality of one bounded slice of the independently imported data. -/
theorem common7Part5 : native7Part5 = ordinary7Part5 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge7Part5
    (backEqual : ∀ n, getFromBlocks native7Rest5.toList n = getFromBlocks ordinary7Rest5.toList n)
    (n : Nat) : getFromBlocks native7Rest4.toList n = getFromBlocks ordinary7Rest4.toList n := by
  exact split_blocks_agree native7Rest4 ordinary7Rest4 native7Part5 ordinary7Part5
    native7Rest5 ordinary7Rest5 native7Split5 ordinary7Split5 common7Part5 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
