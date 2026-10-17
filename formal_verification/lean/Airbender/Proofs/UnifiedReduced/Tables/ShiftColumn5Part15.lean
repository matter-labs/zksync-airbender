import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn5Part14
import Airbender.Proofs.Tables.BlockSplits
import Airbender.Proofs.Tables.ColumnAgreement

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native5Part15 native5Tail native5Split15 from native5Rest14 at 1534
split_imported_blocks ordinary5Part15 ordinary5Tail ordinary5Split15 from ordinary5Rest14 at 1534
/-- Equality of one bounded slice of the independently imported data. -/
theorem common5Part15 : native5Part15 = ordinary5Part15 := rfl

theorem tail5 : blocksAgree native5Tail.toList ordinary5Tail.toList = true := by
  decide +kernel

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge5Part15
    (backEqual : ∀ n, getFromBlocks native5Tail.toList n = getFromBlocks ordinary5Tail.toList n)
    (n : Nat) : getFromBlocks native5Rest14.toList n = getFromBlocks ordinary5Rest14.toList n := by
  exact split_blocks_agree native5Rest14 ordinary5Rest14 native5Part15 ordinary5Part15
    native5Tail ordinary5Tail native5Split15 ordinary5Split15 common5Part15 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
