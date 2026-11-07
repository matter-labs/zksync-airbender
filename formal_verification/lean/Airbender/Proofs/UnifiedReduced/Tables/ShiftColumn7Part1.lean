import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn7Part0
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native7Part1 native7Rest1 native7Split1 from native7Rest0 at 1542
split_imported_blocks ordinary7Part1 ordinary7Rest1 ordinary7Split1 from ordinary7Rest0 at 1542
/-- Equality of one bounded slice of the independently imported data. -/
theorem common7Part1 : native7Part1 = ordinary7Part1 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge7Part1
    (backEqual : ∀ n, getFromBlocks native7Rest1.toList n = getFromBlocks ordinary7Rest1.toList n)
    (n : Nat) : getFromBlocks native7Rest0.toList n = getFromBlocks ordinary7Rest0.toList n := by
  exact split_blocks_agree native7Rest0 ordinary7Rest0 native7Part1 ordinary7Part1
    native7Rest1 ordinary7Rest1 native7Split1 ordinary7Split1 common7Part1 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
