import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn5Part13
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native5Part14 native5Rest14 native5Split14 from native5Rest13 at 1534
split_imported_blocks ordinary5Part14 ordinary5Rest14 ordinary5Split14 from ordinary5Rest13 at 1534
/-- Equality of one bounded slice of the independently imported data. -/
theorem common5Part14 : native5Part14 = ordinary5Part14 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge5Part14
    (backEqual : ∀ n, getFromBlocks native5Rest14.toList n = getFromBlocks ordinary5Rest14.toList n)
    (n : Nat) : getFromBlocks native5Rest13.toList n = getFromBlocks ordinary5Rest13.toList n := by
  exact split_blocks_agree native5Rest13 ordinary5Rest13 native5Part14 ordinary5Part14
    native5Rest14 ordinary5Rest14 native5Split14 ordinary5Split14 common5Part14 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
