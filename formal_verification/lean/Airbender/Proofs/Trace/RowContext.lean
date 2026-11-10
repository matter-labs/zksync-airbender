import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Helpers.Context.RowContext
import Airbender.Proofs.Trace.PooledHistory
import Airbender.Proofs.Trace.Retirement
import Airbender.Proofs.Trace.PortReads

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

theorem register_history_projection_at {p : Nat}
    {cells : List Cell} {columns : TraceColumns} {first second destination : MemoryPort}
    {w : Nat → ZMod p} {rd : BitVec 5} (epoch : Nat)
    (firstReadonly : first.writeValue = none) (secondReadonly : second.writeValue = none)
    (address : destination.address.code w = (Cell.register rd).addressCode) (output : Output)
    (data : output.destination.toBitVec = memoryWord (destination.writeCode w))
    {before after : State}
    (history : SailHistory cells
      (nativeRowEvents epoch columns #[first, second, destination] w).reverse before after) :
    run (projectedStep (.Regidx rd) output) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after output.pc.toBitVec) := by
  have written := native_history_write epoch rfl firstReadonly secondReadonly history
    (port := destination) rfl address
  rw [← data] at written
  exact projected_step_of_write rd output written

/-- Shared register-effect projection for three-port rows. The destination
    index and data equations are observable wiring, not instruction behavior. -/
theorem register_history_projection {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 32)
    {cells : List Cell} {columns : TraceColumns} {first second destination : MemoryPort}
    {w : Nat → ZMod p} {rd : BitVec 5} {index : Nat} (epoch : Nat)
    (firstReadonly : first.writeValue = none) (secondReadonly : second.writeValue = none)
    (register : destination.address = .register index)
    (rdColumn : w index = (rd.toNat : ZMod p)) (output : Output)
    (data : output.destination.toBitVec = memoryWord (destination.writeCode w))
    {before after : State}
    (history : SailHistory cells
      (nativeRowEvents epoch columns #[first, second, destination] w).reverse before after) :
    run (projectedStep (.Regidx rd) output) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after output.pc.toBitVec) := by
  have indexBound : rd.toNat < p := by have small := rd.isLt; omega
  have address : destination.address.code w = (Cell.register rd).addressCode := by
    simp [register, MemoryAddress.code, Cell.addressCode, rdColumn,
      ZMod.val_natCast, Nat.mod_eq_of_lt indexBound]
  exact register_history_projection_at epoch firstReadonly secondReadonly address output data history

theorem row_context_of_history {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    {trace : Data p Kind} {initial : State} {cells : List Cell}
    {rows : List (Row p Kind)} {final : State}
    (rowsPermutation : rows.Perm trace.rows)
    (rowsOrdered : rows.Pairwise (fun a b => b.clock < a.clock))
    (native : SailHistory cells
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) initial final)
    (eventsProjection :
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents)
    {row : Row p Kind} {before : State}
    (position : RowPosition trace initial cells row before) :
    ∃ events rawBefore rawAfter,
      (∀ event ∈ events, event ∈ trace.nativeEvents) ∧
      SailHistory cells events initial rawBefore ∧
      SailHistory cells (rowEvents trace.memoryEpoch row).reverse rawBefore rawAfter ∧
      before = retiredState rawBefore row.start.word.toBitVec := by
  obtain ⟨newer, older, middle, permutation, ordered, writes, state⟩ := position
  have same : rows = newer ++ row :: older :=
    List.Perm.eq_of_pairwise' rowsOrdered ordered (rowsPermutation.trans permutation.symm)
  rw [same, List.flatMap_append, List.flatMap_cons] at native
  obtain ⟨currentEnd, tailHistory, _⟩ := sail_history_append.mp native
  obtain ⟨currentStart, past, current⟩ := sail_history_append.mp tailHistory
  have canonicalWrites : WriteHistory cells (older.flatMap rowWriteValues) initial currentStart := by
    have projected := SailHistory.writes past
    simpa only [List.map_flatMap, row_write_values] using projected
  have equal := WriteHistory.unique canonicalWrites writes
  subst currentStart
  refine ⟨_, middle, currentEnd, ?_, past, current, state⟩
  intro event present
  apply eventsProjection.mem_iff.mp
  rw [same, List.flatMap_append, List.flatMap_cons]
  simp only [List.mem_append]
  exact Or.inr (Or.inr present)

theorem row_position_of_history {Kind : Type} [CircuitLayout Kind] [Fact p.Prime]
    {trace : Data p Kind} {initial : State} {cells : List Cell}
    {rows : List (Row p Kind)} {final : State}
    (permutation : rows.Perm trace.rows)
    (ordered : rows.Pairwise (fun a b => b.clock < a.clock))
    (native : SailHistory cells
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) initial final)
    {row : Row p Kind} (member : row ∈ trace.rows) :
    ∃ before, RowPosition trace initial cells row before := by
  obtain ⟨newer, older, same⟩ := List.mem_iff_append.mp (permutation.mem_iff.mpr member)
  rw [same, List.flatMap_append, List.flatMap_cons] at native
  obtain ⟨currentEnd, tailHistory, _⟩ := sail_history_append.mp native
  obtain ⟨currentStart, past, _⟩ := sail_history_append.mp tailHistory
  refine ⟨retiredState currentStart row.start.word.toBitVec,
    newer, older, currentStart, same ▸ permutation, same ▸ ordered, ?_, rfl⟩
  have writes := SailHistory.writes past
  simpa only [List.map_flatMap, row_write_values] using writes

/-- Recover actual reads at any selected position using the complete initialized
    pooled history. The caller supplies only a write-only state representation. -/
theorem pooled_row_context {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase) (inverse : SerializedInverse.Clock p)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (distinct : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : pooledProgramImage initial addresses = some program)
    (decoded : PooledDecoded trace program) {row : Row p PooledFamily} {before : State}
    (position : RowPosition trace initial cells row before) :
    ∃ events rawBefore rawAfter,
      (∀ event ∈ events, event ∈ trace.nativeEvents) ∧
      SailHistory cells events initial rawBefore ∧
      SailHistory cells (rowEvents trace.memoryEpoch row).reverse rawBefore rawAfter ∧
      before = retiredState rawBefore row.start.word.toBitVec := by
  obtain ⟨history, rows, final, consistent, rowsPermutation, rowsOrdered, native, matched⟩ :=
    pooled_native_history hp inverse accepted clocks image distinct aligned programImage decoded
  have projection :
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
    rw [native_events_projection hp inverse accepted clocks]
    exact rowsPermutation.flatMap (fun row _ => List.reverse_perm _)
  exact row_context_of_history rowsPermutation rowsOrdered native projection position

/-- Normalize the recovered histories to the row's start PC. -/
theorem pooled_row_position {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase) (inverse : SerializedInverse.Clock p)
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
  obtain ⟨events, rawBefore, rawAfter, _, past, current, state⟩ :=
    pooled_row_context hp inverse accepted clocks image distinct aligned programImage decoded position
  subst before
  exact ⟨_, _, retired_state_history past _, retired_state_history current _⟩

/-- Every admitted row has a represented pre-state. The row view does not add
    an existential consistency premise beyond the shared memory argument. -/
theorem pooled_row_position_exists {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase) (inverse : SerializedInverse.Clock p)
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
  exact row_position_of_history permutation ordered native member

end Airbender.Trace.Proofs
