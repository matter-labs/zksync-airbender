import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn5Part6
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native5Part7 native5Rest7 native5Split7 from native5Rest6 at 1534
split_imported_blocks ordinary5Part7 ordinary5Rest7 ordinary5Split7 from ordinary5Rest6 at 1534
/-- Equality of one bounded slice of the independently imported data. -/
theorem common5Part7 : native5Part7 = ordinary5Part7 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge5Part7
    (backEqual : ∀ n, getFromBlocks native5Rest7.toList n = getFromBlocks ordinary5Rest7.toList n)
    (n : Nat) : getFromBlocks native5Rest6.toList n = getFromBlocks ordinary5Rest6.toList n := by
  exact split_blocks_agree native5Rest6 ordinary5Rest6 native5Part7 ordinary5Part7
    native5Rest7 ordinary5Rest7 native5Split7 ordinary5Split7 common5Part7 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
