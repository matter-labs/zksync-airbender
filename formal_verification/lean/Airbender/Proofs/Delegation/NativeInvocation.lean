import Airbender.Review.Helpers.Delegation.Requests
import Airbender.Proofs.Trace.Timestamps
import Airbender.Proofs.Constraints

namespace Airbender.Delegation.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- The current native timestamp query excludes an active worker whose raw
    invocation is zero. This uses the imported constraint, not a positive-clock
    interface or an assumed caller occurrence. -/
theorem active_invocation_live [Fact babyBearModulus.Prime]
    {setup : Setup babyBearModulus} {row : Row babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints setup))
    (active : row.assignment row.columns.execute = 1) :
    Requests.Live (Requests.fulfillment row) := by
  intro zero
  have low := congrArg Prod.fst zero
  rcases row with ⟨family, w⟩
  cases family
  all_goals change w 1 = 0 at low
  all_goals change w 0 = 1 at active
  all_goals dsimp only [Row.constraints, Bigint.clockConstraints, Blake2G.clockConstraints,
    Blake2Round.clockConstraints, Keccak.clockConstraints] at h
  all_goals
    have timestamps := Verification.holds_of_sublist h
      (List.sublist_append_right _ _)
    have bound := Trace.Proofs.range_bound
      (Verification.lookup_of_holds timestamps ⟨0, by exact Nat.zero_lt_succ _⟩)
    norm_num [Expression.eval, Verification.environment, active, low,
      ZMod.val_natCast, babyBearModulus] at bound
    change (503316480 : ZMod babyBearModulus).val < 524288 at bound
    have value : (503316480 : ZMod babyBearModulus).val = 503316480 := rfl
    rw [value] at bound
    omega

end Airbender.Delegation.Proofs
