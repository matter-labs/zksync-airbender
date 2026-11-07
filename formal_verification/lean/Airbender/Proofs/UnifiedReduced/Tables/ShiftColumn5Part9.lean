import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn5Part8
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native5Part9 native5Rest9 native5Split9 from native5Rest8 at 1534
split_imported_blocks ordinary5Part9 ordinary5Rest9 ordinary5Split9 from ordinary5Rest8 at 1534
/-- Equality of one bounded slice of the independently imported data. -/
theorem common5Part9 : native5Part9 = ordinary5Part9 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge5Part9
    (backEqual : ∀ n, getFromBlocks native5Rest9.toList n = getFromBlocks ordinary5Rest9.toList n)
    (n : Nat) : getFromBlocks native5Rest8.toList n = getFromBlocks ordinary5Rest8.toList n := by
  exact split_blocks_agree native5Rest8 ordinary5Rest8 native5Part9 ordinary5Part9
    native5Rest9 ordinary5Rest9 native5Split9 ordinary5Split9 common5Part9 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
