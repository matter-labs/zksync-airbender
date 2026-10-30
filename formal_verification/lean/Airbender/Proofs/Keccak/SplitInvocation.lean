import Airbender.Review.Trace.Workers.Keccak.SplitRequests
import Airbender.Proofs.Trace.Timestamps
import Airbender.Proofs.Constraints

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- The native initial timestamp query excludes an unissued zero-clock split worker. -/
theorem active_invocation_live [Fact babyBearModulus.Prime]
    {setup : Setup babyBearModulus} {row : Row babyBearModulus} (cached : Bool)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints cached setup))
    (active : row.assignment (row.columns cached).execute = 1) :
    Delegation.Requests.Live (row.fulfillment cached) := by
  intro zero
  have low := congrArg Prod.fst zero
  rcases row with ⟨kind, w⟩
  cases cached <;> cases kind
  all_goals change w 1 = 0 at low
  all_goals change w 0 = 1 at active
  all_goals dsimp only [Row.constraints, ColumnParity.clockConstraints, ThetaRho.clockConstraints,
    Chi5.clockConstraints, ColumnParityCached.clockConstraints, ThetaRhoCached.clockConstraints,
    Chi5Cached.clockConstraints] at holds
  all_goals
    have timestamps := Verification.holds_of_sublist holds (List.sublist_append_right _ _)
    have bound := Trace.Proofs.range_bound
      (Verification.lookup_of_holds timestamps ⟨0, by exact Nat.zero_lt_succ _⟩)
    norm_num [Expression.eval, Verification.environment, active, low,
      ZMod.val_natCast, babyBearModulus] at bound
    change (503316480 : ZMod babyBearModulus).val < 524288 at bound
    have value : (503316480 : ZMod babyBearModulus).val = 503316480 := rfl
    rw [value] at bound
    omega

end Airbender.Keccak.Split.Native.Proofs
