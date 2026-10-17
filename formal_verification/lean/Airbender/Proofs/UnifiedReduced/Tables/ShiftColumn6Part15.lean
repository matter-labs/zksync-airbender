import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn6Part14
import Airbender.Proofs.Tables.BlockSplits
import Airbender.Proofs.Tables.ColumnAgreement

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native6Part15 native6Tail native6Split15 from native6Rest14 at 1518
split_imported_blocks ordinary6Part15 ordinary6Tail ordinary6Split15 from ordinary6Rest14 at 1518
/-- Equality of one bounded slice of the independently imported data. -/
theorem common6Part15 : native6Part15 = ordinary6Part15 := rfl

theorem tail6 : blocksAgree native6Tail.toList ordinary6Tail.toList = true := by
  decide +kernel

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge6Part15
    (backEqual : ∀ n, getFromBlocks native6Tail.toList n = getFromBlocks ordinary6Tail.toList n)
    (n : Nat) : getFromBlocks native6Rest14.toList n = getFromBlocks ordinary6Rest14.toList n := by
  exact split_blocks_agree native6Rest14 ordinary6Rest14 native6Part15 ordinary6Part15
    native6Tail ordinary6Tail native6Split15 ordinary6Split15 common6Part15 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
