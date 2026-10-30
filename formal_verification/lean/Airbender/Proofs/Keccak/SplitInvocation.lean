import Airbender.Review.Trace.Workers.Keccak.SplitRequests
import Airbender.Proofs.Trace.Timestamps
import Airbender.Proofs.Constraints
import Airbender.Proofs.Keccak.SplitRequests

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

/-- Exact request matching accounts for every active split fulfillment. -/
theorem native_requests_match [Fact babyBearModulus.Prime]
    {data : RequestTrace babyBearModulus} (accepted : RequestChecks data)
    {initial : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (inputs : RequestInputs data initial addresses) : data.calls.Perm data.fulfillments := by
  have binding := request_clock_binding (by decide) (by decide) accepted inputs
  have all : data.fulfillments.filter (fun request => decide (Delegation.Requests.Live request)) =
      data.fulfillments := by
    apply List.filter_eq_self.mpr
    intro request member
    obtain ⟨worker, present, rfl⟩ := List.mem_map.mp member
    exact decide_eq_true (active_invocation_live data.workers.cached
      (accepted.workerEquations.rowsHold worker present) (accepted.workerActive worker present))
  exact all ▸ binding.fulfilled

/-- Every actual split worker has a caller at its exact native request. -/
theorem native_worker_caller [Fact babyBearModulus.Prime]
    {data : RequestTrace babyBearModulus} (accepted : RequestChecks data)
    {initial : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (inputs : RequestInputs data initial addresses)
    {worker : Row babyBearModulus} (member : worker ∈ data.workers.rows) :
    ∃ caller ∈ data.callers,
      worker.fulfillment data.workers.cached = Delegation.Requests.caller caller.assignment := by
  have matched := native_requests_match accepted inputs
  obtain ⟨caller, present, equal⟩ := List.mem_map.mp
    (matched.mem_iff.mpr (List.mem_map.mpr ⟨worker, member, rfl⟩))
  exact ⟨caller, present, equal.symm⟩

end Airbender.Keccak.Split.Native.Proofs
