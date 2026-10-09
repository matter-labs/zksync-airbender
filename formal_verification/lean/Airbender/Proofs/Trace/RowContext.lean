import Airbender.Review.Trace.RowContext
import Airbender.Proofs.Trace.PooledHistory
import Airbender.Proofs.Trace.Retirement

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail

theorem SailHistory.writes {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after) :
    WriteHistory cells (events.map fun event => (event.2.1, event.2.2.2)) before after := by
  induction history with
  | nil => exact .nil _
  | cons past cell member address read written ih =>
    exact .cons ih cell member address written

/-- The write-only state mapping is deterministic. It has no read premise. -/
theorem WriteHistory.unique {cells : List Cell} {values : List (Nat × Nat)}
    {before left right : State} (a : WriteHistory cells values before left)
    (b : WriteHistory cells values before right) : left = right := by
  induction a generalizing right with
  | nil => cases b; rfl
  | cons past cell member address write ih =>
    cases b with
    | cons other second secondMember secondAddress secondWrite =>
      have sameCell : cell = second := cell_address_injective (address.trans secondAddress.symm)
      have sameState := ih other
      subst second
      subst sameState
      exact (EStateM.Result.ok.inj (write.symm.trans secondWrite)).2

theorem row_write_values {Kind : Type} [CircuitLayout Kind] (epoch : Nat) (row : Row p Kind) :
    ((rowEvents epoch row).reverse.map fun event => (event.2.1, event.2.2.2)) = rowWriteValues row := by
  simp [rowEvents, nativeRowEvents, rowWriteValues, Row.writes, writeToken,
    List.map_reverse, List.map_map, Function.comp_def]

/-- Recover actual reads at any selected position using the complete initialized
    pooled history. The caller supplies only a write-only state representation. -/
theorem pooled_row_position {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (distinct : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : pooledProgramImage initial addresses = some program)
    (decoded : PooledDecoded trace program) {row : Row p PooledFamily} {before : State}
    (position : RowPosition trace initial cells row before) :
    ∃ events after,
      SailHistory cells events (retiredState initial row.start.word.toBitVec) before ∧
      SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after := by
  obtain ⟨newer, older, middle, permutation, ordered, writes, state⟩ := position
  obtain ⟨history, rows, final, consistent, rowsPermutation, rowsOrdered, native, matched⟩ :=
    pooled_native_history hp inverse accepted clocks image distinct aligned programImage decoded
  have same : rows = newer ++ row :: older :=
    List.Perm.eq_of_pairwise' rowsOrdered ordered (rowsPermutation.trans permutation.symm)
  rw [same, List.flatMap_append, List.flatMap_cons] at native
  obtain ⟨currentEnd, tailHistory, _⟩ := sail_history_append.mp native
  obtain ⟨currentStart, past, current⟩ := sail_history_append.mp tailHistory
  have canonicalWrites : WriteHistory cells (older.flatMap rowWriteValues) initial currentStart := by
    have projected := past.writes
    simpa only [List.map_flatMap, row_write_values] using projected
  have equal := WriteHistory.unique canonicalWrites writes
  subst currentStart
  subst before
  exact ⟨_, _, retired_state_history past _, retired_state_history current _⟩

/-- Every admitted row has a represented pre-state. The row view does not add
    an existential consistency premise beyond the shared memory argument. -/
theorem pooled_row_position_exists {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (distinct : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : pooledProgramImage initial addresses = some program)
    (decoded : PooledDecoded trace program) {row : Row p PooledFamily}
    (member : row ∈ trace.rows) : ∃ before, RowPosition trace initial cells row before := by
  obtain ⟨history, rows, final, consistent, permutation, ordered, native, matched⟩ :=
    pooled_native_history hp inverse accepted clocks image distinct aligned programImage decoded
  obtain ⟨newer, older, same⟩ := List.mem_iff_append.mp (permutation.mem_iff.mpr member)
  rw [same, List.flatMap_append, List.flatMap_cons] at native
  obtain ⟨currentEnd, tailHistory, _⟩ := sail_history_append.mp native
  obtain ⟨currentStart, past, _⟩ := sail_history_append.mp tailHistory
  refine ⟨retiredState currentStart row.start.word.toBitVec,
    newer, older, currentStart, same ▸ permutation, same ▸ ordered, ?_, rfl⟩
  have writes := past.writes
  simpa only [List.map_flatMap, row_write_values] using writes

end Airbender.Trace.Proofs
