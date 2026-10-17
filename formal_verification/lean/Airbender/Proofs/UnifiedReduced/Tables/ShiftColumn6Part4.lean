import Airbender.Proofs.UnifiedReduced.Tables.ShiftColumn6Part3
import Airbender.Proofs.Tables.BlockSplits

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

split_imported_blocks native6Part4 native6Rest4 native6Split4 from native6Rest3 at 1518
split_imported_blocks ordinary6Part4 ordinary6Rest4 ordinary6Split4 from ordinary6Rest3 at 1518
/-- Equality of one bounded slice of the independently imported data. -/
theorem common6Part4 : native6Part4 = ordinary6Part4 := rfl

/-- A bounded equality composes with the remaining imported suffix. -/
theorem bridge6Part4
    (backEqual : ∀ n, getFromBlocks native6Rest4.toList n = getFromBlocks ordinary6Rest4.toList n)
    (n : Nat) : getFromBlocks native6Rest3.toList n = getFromBlocks ordinary6Rest3.toList n := by
  exact split_blocks_agree native6Rest3 ordinary6Rest3 native6Part4 ordinary6Part4
    native6Rest4 ordinary6Rest4 native6Split4 ordinary6Split4 common6Part4 backEqual n

end Airbender.UnifiedReduced.Setup.Proofs
