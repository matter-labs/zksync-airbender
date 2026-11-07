import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn7Part14
import Airbender.Proofs.Tables.BlockSplits
import Airbender.Proofs.Tables.ColumnAgreement

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native7Part15 native7Tail native7Split15 from native7Rest14 at 1542
split_imported_blocks ordinary7Part15 ordinary7Tail ordinary7Split15 from ordinary7Rest14 at 1542
/-- Equality of one bounded slice of the independently imported data. -/
theorem common7Part15 : native7Part15 = ordinary7Part15 := rfl

theorem tail7 : blocksAgree native7Tail.toList ordinary7Tail.toList = true := by
  decide +kernel

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge7Part15
    (backEqual : ∀ n, getFromBlocks native7Tail.toList n = getFromBlocks ordinary7Tail.toList n)
    (n : Nat) : getFromBlocks native7Rest14.toList n = getFromBlocks ordinary7Rest14.toList n := by
  exact split_blocks_agree native7Rest14 ordinary7Rest14 native7Part15 ordinary7Part15
    native7Tail ordinary7Tail native7Split15 ordinary7Split15 common7Part15 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
