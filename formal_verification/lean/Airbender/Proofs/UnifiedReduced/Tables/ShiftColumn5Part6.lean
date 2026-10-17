import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn5Part5
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native5Part6 native5Rest6 native5Split6 from native5Rest5 at 1534
split_imported_blocks ordinary5Part6 ordinary5Rest6 ordinary5Split6 from ordinary5Rest5 at 1534
/-- Equality of one bounded slice of the independently imported data. -/
theorem common5Part6 : native5Part6 = ordinary5Part6 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge5Part6
    (backEqual : ∀ n, getFromBlocks native5Rest6.toList n = getFromBlocks ordinary5Rest6.toList n)
    (n : Nat) : getFromBlocks native5Rest5.toList n = getFromBlocks ordinary5Rest5.toList n := by
  exact split_blocks_agree native5Rest5 ordinary5Rest5 native5Part6 ordinary5Part6
    native5Rest6 ordinary5Rest6 native5Split6 ordinary5Split6 common5Part6 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
