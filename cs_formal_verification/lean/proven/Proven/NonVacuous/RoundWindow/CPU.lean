module
public import Proven.NonVacuous.RoundWindow.Program

@[expose] public section
namespace Airbender.NonVacuous.RoundWindow
open Trace Trace.Machine HashCallers
set_option warningAsError true

/-- The unified block fits the PC, timestamp and x0 ordering bounds. -/
theorem room : FamilyCallers.Block.Room 0 4 0 10 := by
  constructor <;> decide

/-- Every submitted worker row satisfies the full round circuit and participates. -/
theorem workers_accepted : WorkersAccepted workers where
  standardConstraints := (Blake2RoundSpan.accepted_from start).constraints
  standardActive := Blake2RoundSpan.execute_from
  splitConstraints := by intro row member; cases member
  splitActive := by intro row member; cases member

/-- Every unrolled CPU row satisfies its actual imported constraints. -/
theorem unrolled_constraints : ∀ row ∈ unrolledTrace.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints unrolledTrace.rom) := by
  intro row member
  obtain ⟨index, bound, rfl⟩ := unrolled_mem_rows member
  exact unrolled_satisfies (unrolled_valid bound)

/-- Every unrolled CPU row participates. -/
theorem unrolled_active_rows : ∀ row ∈ unrolledTrace.rows, row.assignment row.columns.execute = 1 := by
  intro row member
  obtain ⟨index, _, rfl⟩ := unrolled_mem_rows member
  exact unrolled_active index

/-- The native unrolled states form one ten-instruction path. -/
theorem unrolled_states :
    (unrolledTrace.initial :: unrolledTrace.rows.map Row.finish).Perm
      (unrolledTrace.terminal :: unrolledTrace.rows.map Row.start) := by
  change ((unrolledRow 0).start :: ((List.range 10).map unrolledRow).map Row.finish).Perm
    ((unrolledRow 9).finish :: ((List.range 10).map unrolledRow).map Row.start)
  simp only [List.map_map]
  exact chain_perm (start := fun index => (unrolledRow index).start)
    (finish := fun index => (unrolledRow index).finish) 9 fun index _ => by
      change (PooledRow.row (4 * index) (4 + 4 * index) (previousOf 0 4 index)).finish =
        (PooledRow.row (4 * (index + 1)) (4 + 4 * (index + 1)) (previousOf 0 4 (index + 1))).start
      rw [PooledRow.finish_start _ _ _ (previousOf 0 4 (index + 1))]
      congr 2

/-- Every submitted unified CPU row satisfies its actual imported constraints. -/
theorem unified_constraints : ∀ row ∈ unifiedTrace.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints unifiedTrace.rom) :=
  FamilyCallers.Block.satisfies room initial

/-- Every unified CPU row participates. -/
theorem unified_active_rows : ∀ row ∈ unifiedTrace.rows, row.assignment row.columns.execute = 1 :=
  FamilyCallers.Block.active

/-- The native unified states form the same ten-instruction path. -/
theorem unified_states :
    (unifiedTrace.initial :: unifiedTrace.rows.map Row.finish).Perm
      (unifiedTrace.terminal :: unifiedTrace.rows.map Row.start) :=
  FamilyCallers.Block.states (g := .blakeRound) (f := 0) (c0 := 4) (p0 := 0) 9

/-- The unrolled callers issue the ten complete round requests in order. -/
theorem unrolled_calls :
    (unrolledCallers unrolledTrace).map (fun row => Delegation.Requests.caller row.assignment) =
      (List.range 10).map (requestAt .blakeRound 4) := by decide +kernel

/-- The unified callers issue the same ten complete round requests in order. -/
theorem unified_calls :
    (unifiedTrace.rows.filter (fun row => decide (UnifiedReduced.Caller.Selected row.assignment))).map
      (fun row => UnifiedReduced.Caller.request row.assignment) =
      (List.range 10).map (requestAt .blakeRound 4) := by
  rw [show unifiedTrace.rows = FamilyCallers.Block.callerRows .blakeRound 0 4 0 10 from rfl,
    FamilyCallers.Block.filter_selected]
  exact FamilyCallers.Block.requests

/-- The round worker span fulfills each caller request once in order. -/
theorem worker_fulfillments : workers.fulfillments = (List.range 10).map (requestAt .blakeRound 4) := by
  change ((Blake2RoundSpan.rowsFrom Blake2RoundSpan.seed 5 10).map Delegation.Requests.fulfillment ++ []) = _
  rw [List.append_nil]
  exact fulfillments (row := Blake2RoundSpan.rowFrom Blake2RoundSpan.seed 5)
    (fun _ => rfl) (Blake2RoundSpan.invocation_raw Blake2RoundSpan.seed 5)

/-- The unrolled virtual request tokens balance with every submitted worker. -/
theorem unrolled_requests : Delegation.Requests.Matching
    ((unrolledCallers unrolledTrace).map fun row => Delegation.Requests.caller row.assignment)
    workers.fulfillments := by
  rw [unrolled_calls, worker_fulfillments, Delegation.Requests.Matching]
  exact List.perm_append_comm

/-- The unified virtual request tokens have the same exact matching. -/
theorem unified_requests : Delegation.Requests.Matching
    ((unifiedTrace.rows.filter fun row => decide (UnifiedReduced.Caller.Selected row.assignment)).map
      fun row => UnifiedReduced.Caller.request row.assignment) workers.fulfillments := by
  rw [unified_calls, worker_fulfillments, Delegation.Requests.Matching]
  exact List.perm_append_comm

end Airbender.NonVacuous.RoundWindow
