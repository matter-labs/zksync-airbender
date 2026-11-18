module
public import Proven.Trace.Machine.CodeWindowCore
public import Proven.Trace.Machine.DecodedCallers
public import Proven.Trace.Machine.Segmentation
public import Proven.Trace.Machine.CallerTimes
public import Proven.Trace.WindowCounts

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Public unrolled code and native clock density derive complete protocol segmentation. -/
theorem unrolled_code_hash_segmentation : UnrolledCodeHashSegmentationClaim := by
  intro config trace workers initialState addresses program windows unrolled image accepted initial aligned separated coverage scopes
  have clocks := state_clock_inputs (by decide) (by decide) accepted.constraints accepted.states initial aligned
  have profile : HashWindowProfile ((unrolledCallers trace).map fun row => Requests.caller row.assignment) windows := by
    apply code_window_profile trace.rows Row.clock
      (fun row => row.family == .addSub && decide (Requests.Selected row.assignment))
      (fun row => Requests.caller row.assignment) windows separated coverage
    · intro row member
      simpa [Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using (clocks row member).2
    · intro row member selected
      have called : row ∈ unrolledCallers trace := List.mem_filter.mpr ⟨member, selected⟩
      unfold requestTick
      rw [unrolled_request_time accepted initial aligned called]
    · intro window member
      have scope := scopes window member
      refine ⟨scope.firstAligned, scope.lastAligned, ?_, ?_⟩
      · have count := native_window_count (by decide) (by decide) accepted.constraints accepted.states initial aligned
          scope.firstAligned scope.lastAligned (by have duration := scope.duration; omega) scope.afterInitial scope.beforeTerminal
        change (trace.rows.filter fun row => decide (window.lower ≤ row.clock ∧ row.clock < window.upper)).length =
          (window.upper - window.lower) / 4 at count
        have duration := scope.duration
        omega
      · intro row included range
        obtain ⟨entry, present, family, query⟩ := accepted.decoded row included
        obtain ⟨kind, admitted, decoded⟩ := scope.code row included range entry present query
        have fields := machine_entry_fields image present decoded
        have caller := unrolled_decoded_caller unrolled (accepted.constraints row included) family fields query
        exact ⟨caller.1, List.mem_map.mpr ⟨kind, admitted, caller.2.symm⟩⟩
  exact hash_segmentation_of_matching (unrolled_requests_complete accepted initial aligned) profile
    (worker_fulfillments_live accepted.toWorkersAccepted)

/-- Public unified code and native clock density derive complete protocol segmentation. -/
theorem unified_code_hash_segmentation : UnifiedCodeHashSegmentationClaim := by
  intro trace workers initialState addresses program windows image accepted initial aligned separated coverage scopes
  have clocks := state_clock_inputs (by decide) (by decide) accepted.constraints accepted.states initial aligned
  have profile : HashWindowProfile ((trace.rows.filter fun row => decide (UnifiedReduced.Caller.Selected row.assignment)).map
      fun row => UnifiedReduced.Caller.request row.assignment) windows := by
    apply code_window_profile trace.rows Row.clock
      (fun row => decide (UnifiedReduced.Caller.Selected row.assignment))
      (fun row => UnifiedReduced.Caller.request row.assignment) windows separated coverage
    · intro row member
      simpa [Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using (clocks row member).2
    · intro row member _
      unfold requestTick
      rw [unified_request_time accepted initial aligned member]
    · intro window member
      have scope := scopes window member
      refine ⟨scope.firstAligned, scope.lastAligned, ?_, ?_⟩
      · have count := native_window_count (by decide) (by decide) accepted.constraints accepted.states initial aligned
          scope.firstAligned scope.lastAligned (by have duration := scope.duration; omega) scope.afterInitial scope.beforeTerminal
        change (trace.rows.filter fun row => decide (window.lower ≤ row.clock ∧ row.clock < window.upper)).length =
          (window.upper - window.lower) / 4 at count
        have duration := scope.duration
        omega
      · intro row included range
        obtain ⟨entry, present, _, query⟩ := accepted.decoded row included
        obtain ⟨kind, admitted, decoded⟩ := scope.code row included range entry present query
        have fields := machine_entry_fields image present decoded
        have caller := unified_decoded_caller (accepted.constraints row included) fields query
        exact ⟨caller.1, List.mem_map.mpr ⟨kind, admitted, caller.2.symm⟩⟩
  exact hash_segmentation_of_matching (unified_requests_complete accepted initial aligned) profile
    (worker_fulfillments_live accepted.toWorkersAccepted)

end Airbender.Trace.Machine.Proofs
