import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn5Part2
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native5Part3 native5Rest3 native5Split3 from native5Rest2 at 1534
split_imported_blocks ordinary5Part3 ordinary5Rest3 ordinary5Split3 from ordinary5Rest2 at 1534
/-- Equality of one bounded slice of the independently imported data. -/
theorem common5Part3 : native5Part3 = ordinary5Part3 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge5Part3
    (backEqual : ∀ n, getFromBlocks native5Rest3.toList n = getFromBlocks ordinary5Rest3.toList n)
    (n : Nat) : getFromBlocks native5Rest2.toList n = getFromBlocks ordinary5Rest2.toList n := by
  exact split_blocks_agree native5Rest2 ordinary5Rest2 native5Part3 ordinary5Part3
    native5Rest3 ordinary5Rest3 native5Split3 ordinary5Split3 common5Part3 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
