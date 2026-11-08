module
public import Human.Trace.Delegation.RVExecution
public import Slop.Delegation.RVBoundaryInputs
public import Slop.Delegation.SailHistory
public import Slop.Trace.RVHistoryFrame

@[expose] public section

/-! Core RV delegation memory execution: every imported delegation access executes once, in native timestamp order,
    as RV cell reads/writes (`RVHistory`) from the public initial `RV.State`. RAM cells are RAM at every address,
    INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`); no `ROM_END` premise.
    Interface for the worker families: `rv_native_memory_execution` (human `RVMemoryInputs`) and
    `rv_native_memory_execution_at_boundary` (proof-level `RVBoundaryInputs`), plus `rv_native_history` (the
    realized history with its final cell matching). -/

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs
set_option warningAsError true

/-- RV sibling of `native_sail_history`: the imported accesses realized as an `RVHistory` from `before`, whose final
    state reads every public cell's latest Clean value. -/
theorem rv_native_history [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : RV.State} {cells : List Cell} (inputs : RVBoundaryInputs data before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList) (events : List MemoryAccess) (after : RV.State),
      history.val.Perm (labeledEvents data) ∧
      events.Perm (data.steps.map transferEvent) ∧
      events.Pairwise (fun a b => b.1 ≤ a.1) ∧
      RVHistory cells events before after ∧ RVStateMatches cells history after := by
  apply Transfer.rv_native_history_at_boundary (SeedProofs.transfer_facts hp accepted inputs.toSeed)
    inputs.transfer aligned
  intro edge present same
  obtain ⟨row, _, step⟩ := List.mem_flatMap.mp present
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp step
  exact False.elim (port_not_zero row (by simpa using portMember) same)

theorem rv_native_memory_execution_at_boundary [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : RV.State} {cells : List Cell}
    (inputs : RVBoundaryInputs data before cells) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    RVMemoryExecution data before cells := by
  obtain ⟨history, events, after, bound, permutation, order, actual, final⟩ :=
    rv_native_history hp accepted inputs aligned
  refine ⟨events, after, permutation, order, actual, ?_, ?_,
    Transfer.rv_terminal_reads_at_boundary (SeedProofs.transfer_facts hp accepted inputs.toSeed)
      inputs.transfer bound final⟩
  · intro edge member
    have access := rv_history_access_execution actual
      (permutation.mem_iff.mpr (List.mem_map.mpr ⟨edge, member, rfl⟩))
    simpa [RVPortExecution, Trace.transferEvent, Trace.memoryWord, Trace.MemoryToken.word] using access
  · intro cell cellAligned untouched value read
    apply rv_history_cell_frame actual aligned cell cellAligned _ read
    intro event member
    obtain ⟨edge, present, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp member)
    exact untouched edge present

/-- The core RV delegation memory execution theorem (statement of `RVNativeMemoryExecutionClaim`). -/
theorem rv_native_memory_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : RV.State} {cells : List Cell}
    (inputs : RVMemoryInputs data before cells) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    RVMemoryExecution data before cells :=
  rv_native_memory_execution_at_boundary hp accepted inputs.toRVBoundaryInputs aligned

end Airbender.Delegation.Proofs
