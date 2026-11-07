import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn6Part13
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native6Part14 native6Rest14 native6Split14 from native6Rest13 at 1518
split_imported_blocks ordinary6Part14 ordinary6Rest14 ordinary6Split14 from ordinary6Rest13 at 1518
/-- Equality of one bounded slice of the independently imported data. -/
theorem common6Part14 : native6Part14 = ordinary6Part14 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge6Part14
    (backEqual : ∀ n, getFromBlocks native6Rest14.toList n = getFromBlocks ordinary6Rest14.toList n)
    (n : Nat) : getFromBlocks native6Rest13.toList n = getFromBlocks ordinary6Rest13.toList n := by
  exact split_blocks_agree native6Rest13 ordinary6Rest13 native6Part14 ordinary6Part14
    native6Rest14 ordinary6Rest14 native6Split14 ordinary6Split14 common6Part14 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
