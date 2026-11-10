import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn5Part7
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native5Part8 native5Rest8 native5Split8 from native5Rest7 at 1533
split_imported_blocks ordinary5Part8 ordinary5Rest8 ordinary5Split8 from ordinary5Rest7 at 1533
/-- Equality of one bounded slice of the independently imported data. -/
theorem common5Part8 : native5Part8 = ordinary5Part8 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge5Part8
    (backEqual : ∀ n, getFromBlocks native5Rest8.toList n = getFromBlocks ordinary5Rest8.toList n)
    (n : Nat) : getFromBlocks native5Rest7.toList n = getFromBlocks ordinary5Rest7.toList n := by
  exact split_blocks_agree native5Rest7 ordinary5Rest7 native5Part8 ordinary5Part8
    native5Rest8 ordinary5Rest8 native5Split8 ordinary5Split8 common5Part8 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
