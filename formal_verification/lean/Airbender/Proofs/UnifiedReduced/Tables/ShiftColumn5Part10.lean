import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn5Part9
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native5Part10 native5Rest10 native5Split10 from native5Rest9 at 1534
split_imported_blocks ordinary5Part10 ordinary5Rest10 ordinary5Split10 from ordinary5Rest9 at 1534
/-- Equality of one bounded slice of the independently imported data. -/
theorem common5Part10 : native5Part10 = ordinary5Part10 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge5Part10
    (backEqual : ∀ n, getFromBlocks native5Rest10.toList n = getFromBlocks ordinary5Rest10.toList n)
    (n : Nat) : getFromBlocks native5Rest9.toList n = getFromBlocks ordinary5Rest9.toList n := by
  exact split_blocks_agree native5Rest9 ordinary5Rest9 native5Part10 ordinary5Part10
    native5Rest10 ordinary5Rest10 native5Split10 ordinary5Split10 common5Part10 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
