import Slop.Trace.RowContext
import Human.Helpers.Context.Registries.Pooled
import Human.Helpers.Decoder.PooledProgram
import Slop.Trace.Pooled
import Slop.Trace.PooledHistory

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail

/-- Recover actual reads at any selected position using the complete initialized
    pooled history. The caller supplies only a write-only state representation. -/
theorem pooled_row_context {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (distinct : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : pooledProgramImage initial addresses = some program)
    (decoded : PooledDecoded trace program) {row : Row p PooledFamily} {before : State}
    (position : RowPosition trace initial cells row before)
    (airbenderConfiguration : Reference.RiscV.Sail.Configured initial := by find_configured) :
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
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (distinct : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : pooledProgramImage initial addresses = some program)
    (decoded : PooledDecoded trace program) {row : Row p PooledFamily} {before : State}
    (position : RowPosition trace initial cells row before)
    (airbenderConfiguration : Reference.RiscV.Sail.Configured initial := by find_configured) :
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
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (distinct : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : pooledProgramImage initial addresses = some program)
    (decoded : PooledDecoded trace program) {row : Row p PooledFamily}
    (member : row ∈ trace.rows)
    (airbenderConfiguration : Reference.RiscV.Sail.Configured initial := by find_configured) : ∃ before, RowPosition trace initial cells row before := by
  obtain ⟨history, rows, final, consistent, permutation, ordered, native, matched⟩ :=
    pooled_native_history hp inverse accepted clocks image distinct aligned programImage decoded
  exact row_position_of_history permutation ordered native member

end Airbender.Trace.Proofs
