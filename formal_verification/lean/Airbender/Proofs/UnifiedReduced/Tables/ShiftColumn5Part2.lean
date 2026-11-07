import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn5Part1
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native5Part2 native5Rest2 native5Split2 from native5Rest1 at 1534
split_imported_blocks ordinary5Part2 ordinary5Rest2 ordinary5Split2 from ordinary5Rest1 at 1534
/-- Equality of one bounded slice of the independently imported data. -/
theorem common5Part2 : native5Part2 = ordinary5Part2 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge5Part2
    (backEqual : ∀ n, getFromBlocks native5Rest2.toList n = getFromBlocks ordinary5Rest2.toList n)
    (n : Nat) : getFromBlocks native5Rest1.toList n = getFromBlocks ordinary5Rest1.toList n := by
  exact split_blocks_agree native5Rest1 ordinary5Rest1 native5Part2 ordinary5Part2
    native5Rest2 ordinary5Rest2 native5Split2 ordinary5Split2 common5Part2 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
