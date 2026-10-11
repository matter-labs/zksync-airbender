import Airbender.Review.UnifiedReduced.Memory
import Airbender.Proofs.UnifiedReduced.Trace
import Airbender.Proofs.Trace.RowContext

namespace Airbender.UnifiedReduced.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem row_position_from_memory [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : UnifiedTrace p}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell} (memory : MemoryExecution trace initial cells)
    {row : Row p UnifiedFamily} {before : State}
    (position : RowPosition trace initial cells row before) :
    ∃ events after,
      SailHistory cells events (retiredState initial row.start.word.toBitVec) before ∧
      SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after := by
  obtain ⟨history, rows, final, consistent, permutation, ordered, native, matched⟩ := memory
  have projection :
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
    rw [native_events_projection hp inverse accepted clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  obtain ⟨events, rawBefore, rawAfter, _, past, current, state⟩ :=
    row_context_of_history permutation ordered native projection position
  subst before
  exact ⟨_, _, retired_state_history past _, retired_state_history current _⟩

theorem row_position_exists_from_memory [Fact p.Prime] {trace : UnifiedTrace p}
    {initial : State} {cells : List Cell} (memory : MemoryExecution trace initial cells)
    {row : Row p UnifiedFamily} (member : row ∈ trace.rows) :
    ∃ before, RowPosition trace initial cells row before := by
  obtain ⟨history, rows, final, consistent, permutation, ordered, native, matched⟩ := memory
  exact row_position_of_history permutation ordered native member

end Airbender.UnifiedReduced.Proofs
