import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn5Part0
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native5Part1 native5Rest1 native5Split1 from native5Rest0 at 1534
split_imported_blocks ordinary5Part1 ordinary5Rest1 ordinary5Split1 from ordinary5Rest0 at 1534
/-- Equality of one bounded slice of the independently imported data. -/
theorem common5Part1 : native5Part1 = ordinary5Part1 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge5Part1
    (backEqual : ∀ n, getFromBlocks native5Rest1.toList n = getFromBlocks ordinary5Rest1.toList n)
    (n : Nat) : getFromBlocks native5Rest0.toList n = getFromBlocks ordinary5Rest0.toList n := by
  exact split_blocks_agree native5Rest0 ordinary5Rest0 native5Part1 ordinary5Part1
    native5Rest1 ordinary5Rest1 native5Split1 ordinary5Split1 common5Part1 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
