import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn7Part13
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native7Part14 native7Rest14 native7Split14 from native7Rest13 at 1542
split_imported_blocks ordinary7Part14 ordinary7Rest14 ordinary7Split14 from ordinary7Rest13 at 1542
/-- Equality of one bounded slice of the independently imported data. -/
theorem common7Part14 : native7Part14 = ordinary7Part14 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge7Part14
    (backEqual : ∀ n, getFromBlocks native7Rest14.toList n = getFromBlocks ordinary7Rest14.toList n)
    (n : Nat) : getFromBlocks native7Rest13.toList n = getFromBlocks ordinary7Rest13.toList n := by
  exact split_blocks_agree native7Rest13 ordinary7Rest13 native7Part14 ordinary7Part14
    native7Rest14 ordinary7Rest14 native7Split14 ordinary7Split14 common7Part14 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
