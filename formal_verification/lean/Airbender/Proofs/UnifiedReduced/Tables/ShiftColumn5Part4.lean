import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn5Part3
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native5Part4 native5Rest4 native5Split4 from native5Rest3 at 1534
split_imported_blocks ordinary5Part4 ordinary5Rest4 ordinary5Split4 from ordinary5Rest3 at 1534
/-- Equality of one bounded slice of the independently imported data. -/
theorem common5Part4 : native5Part4 = ordinary5Part4 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge5Part4
    (backEqual : ∀ n, getFromBlocks native5Rest4.toList n = getFromBlocks ordinary5Rest4.toList n)
    (n : Nat) : getFromBlocks native5Rest3.toList n = getFromBlocks ordinary5Rest3.toList n := by
  exact split_blocks_agree native5Rest3 ordinary5Rest3 native5Part4 ordinary5Part4
    native5Rest4 ordinary5Rest4 native5Split4 ordinary5Split4 common5Part4 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
