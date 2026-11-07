import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn5Part10
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native5Part11 native5Rest11 native5Split11 from native5Rest10 at 1534
split_imported_blocks ordinary5Part11 ordinary5Rest11 ordinary5Split11 from ordinary5Rest10 at 1534
/-- Equality of one bounded slice of the independently imported data. -/
theorem common5Part11 : native5Part11 = ordinary5Part11 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge5Part11
    (backEqual : ∀ n, getFromBlocks native5Rest11.toList n = getFromBlocks ordinary5Rest11.toList n)
    (n : Nat) : getFromBlocks native5Rest10.toList n = getFromBlocks ordinary5Rest10.toList n := by
  exact split_blocks_agree native5Rest10 ordinary5Rest10 native5Part11 ordinary5Part11
    native5Rest11 ordinary5Rest11 native5Split11 ordinary5Split11 common5Part11 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
