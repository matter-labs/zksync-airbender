import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn5Part4
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native5Part5 native5Rest5 native5Split5 from native5Rest4 at 1534
split_imported_blocks ordinary5Part5 ordinary5Rest5 ordinary5Split5 from ordinary5Rest4 at 1534
/-- Equality of one bounded slice of the independently imported data. -/
theorem common5Part5 : native5Part5 = ordinary5Part5 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge5Part5
    (backEqual : ∀ n, getFromBlocks native5Rest5.toList n = getFromBlocks ordinary5Rest5.toList n)
    (n : Nat) : getFromBlocks native5Rest4.toList n = getFromBlocks ordinary5Rest4.toList n := by
  exact split_blocks_agree native5Rest4 ordinary5Rest4 native5Part5 ordinary5Part5
    native5Rest5 ordinary5Rest5 native5Split5 ordinary5Split5 common5Part5 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
