import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn7Part3
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native7Part4 native7Rest4 native7Split4 from native7Rest3 at 1542
split_imported_blocks ordinary7Part4 ordinary7Rest4 ordinary7Split4 from ordinary7Rest3 at 1542
/-- Equality of one bounded slice of the independently imported data. -/
theorem common7Part4 : native7Part4 = ordinary7Part4 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge7Part4
    (backEqual : ∀ n, getFromBlocks native7Rest4.toList n = getFromBlocks ordinary7Rest4.toList n)
    (n : Nat) : getFromBlocks native7Rest3.toList n = getFromBlocks ordinary7Rest3.toList n := by
  exact split_blocks_agree native7Rest3 ordinary7Rest3 native7Part4 ordinary7Part4
    native7Rest4 ordinary7Rest4 native7Split4 ordinary7Split4 common7Part4 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
