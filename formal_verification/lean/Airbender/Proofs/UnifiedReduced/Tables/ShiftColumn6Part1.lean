import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn6Part0
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native6Part1 native6Rest1 native6Split1 from native6Rest0 at 1518
split_imported_blocks ordinary6Part1 ordinary6Rest1 ordinary6Split1 from ordinary6Rest0 at 1518
/-- Equality of one bounded slice of the independently imported data. -/
theorem common6Part1 : native6Part1 = ordinary6Part1 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge6Part1
    (backEqual : ∀ n, getFromBlocks native6Rest1.toList n = getFromBlocks ordinary6Rest1.toList n)
    (n : Nat) : getFromBlocks native6Rest0.toList n = getFromBlocks ordinary6Rest0.toList n := by
  exact split_blocks_agree native6Rest0 ordinary6Rest0 native6Part1 ordinary6Part1
    native6Rest1 ordinary6Rest1 native6Split1 ordinary6Split1 common6Part1 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
