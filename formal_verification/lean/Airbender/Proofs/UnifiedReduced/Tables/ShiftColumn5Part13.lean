import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn5Part12
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native5Part13 native5Rest13 native5Split13 from native5Rest12 at 1534
split_imported_blocks ordinary5Part13 ordinary5Rest13 ordinary5Split13 from ordinary5Rest12 at 1534
/-- Equality of one bounded slice of the independently imported data. -/
theorem common5Part13 : native5Part13 = ordinary5Part13 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge5Part13
    (backEqual : ∀ n, getFromBlocks native5Rest13.toList n = getFromBlocks ordinary5Rest13.toList n)
    (n : Nat) : getFromBlocks native5Rest12.toList n = getFromBlocks ordinary5Rest12.toList n := by
  exact split_blocks_agree native5Rest12 ordinary5Rest12 native5Part13 ordinary5Part13
    native5Rest13 ordinary5Rest13 native5Split13 ordinary5Split13 common5Part13 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
