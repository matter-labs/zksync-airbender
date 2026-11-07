import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn5Part11
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native5Part12 native5Rest12 native5Split12 from native5Rest11 at 1534
split_imported_blocks ordinary5Part12 ordinary5Rest12 ordinary5Split12 from ordinary5Rest11 at 1534
/-- Equality of one bounded slice of the independently imported data. -/
theorem common5Part12 : native5Part12 = ordinary5Part12 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge5Part12
    (backEqual : ∀ n, getFromBlocks native5Rest12.toList n = getFromBlocks ordinary5Rest12.toList n)
    (n : Nat) : getFromBlocks native5Rest11.toList n = getFromBlocks ordinary5Rest11.toList n := by
  exact split_blocks_agree native5Rest11 ordinary5Rest11 native5Part12 ordinary5Part12
    native5Rest12 ordinary5Rest12 native5Split12 ordinary5Split12 common5Part12 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
