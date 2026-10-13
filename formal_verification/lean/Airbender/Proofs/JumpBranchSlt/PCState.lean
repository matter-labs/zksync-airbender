import Airbender.Review.Helpers.PCState.Theorems
import Airbender.Proofs.JumpBranchSlt

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic

theorem final_pc_low_bound {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w Variables.finalPCLo).val < limbBase := by
  have low := (local_ranges h).2.2.2
  have cleanup := (lookup_values hp h).2.2.2.2
  rw [cleanup, ZMod.val_natCast_of_lt (by
    dsimp [limbBase] at low
    omega : (w 36).val - (w 36).val % 4 < p)]
  exact lt_of_le_of_lt (Nat.sub_le _ _) low

/-- One range discharge serves comparisons, branches and both jump selectors. -/
theorem final_pc_bounds {p n : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {context : PCState.Context p n} {w : Nat → ZMod p}
    (global : PCState.Interface context)
    (outgoing : PCState.Outgoing context (w Variables.finalPCLo, w Variables.finalPCHi))
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w Variables.finalPCLo).val < limbBase ∧ (w Variables.finalPCHi).val < limbBase :=
  PCState.outgoing_bounds (by dsimp [limbBase]; omega) global outgoing (final_pc_low_bound hp h)

end Airbender.JumpBranchSlt.Proofs
