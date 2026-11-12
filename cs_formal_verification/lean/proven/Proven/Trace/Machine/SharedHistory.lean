module
public import Proven.Trace.Machine.UnrolledZeroRules
public import Proven.Trace.Machine.UnifiedZeroRules
public import Proven.Delegation.RVSharedImage

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Shared memory matching yields one actual RV history and the terminal reads of that history. -/
theorem shared_history {data : Transfer.Data babyBearModulus} {initial : RV.State} {cells : List Cell}
    (facts : Transfer.Facts data) (image : initialImageRV initial cells = some data.initial)
    (distinct : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (rules : Transfer.CellWriteRules data (Cell.register 0).addressCode 0) :
    ∃ (events : List MemoryAccess) (final : RV.State),
      events.Perm (data.steps.map transferEvent) ∧
      events.Pairwise (fun a b => b.1 ≤ a.1) ∧ RVHistory cells events initial final ∧
      (∀ sink ∈ data.terminal, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.readRV final = some (memoryWord sink.value)) := by
  have inputs := Transfer.rv_boundary_inputs image (distinct.map cell_address_injective)
  have initialZero := Transfer.rv_initial_zero image
  have reads := Transfer.read_cell_values_of_rules facts _ _ initialZero rules
  have writes : ∀ edge ∈ data.steps, edge.1.address = (Cell.register 0).addressCode →
      memoryWord edge.2.value = 0 := by
    intro edge member address
    have value := rules edge member address (fun source present _ same => reads source present same)
    rw [value]
    rfl
  obtain ⟨history, events, final, bound, permutation, ordered, actual, finalReads⟩ :=
    Transfer.rv_native_history_at_boundary facts inputs aligned writes
  exact ⟨events, final, permutation, ordered, actual,
    Transfer.rv_terminal_reads_at_boundary facts inputs bound finalReads⟩

/-- The unrolled CPU and both worker pools share one RV history from the public seed image. -/
theorem unrolled_shared_history {config : RVMachineConfig} (unrolled : config ≠ .unified)
    {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} {initialState : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (alignedClock : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (image : initialImageRV initialState cells = some trace.initialMemory)
    (distinct : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (programImage : rvMachineProgramImage config initialState addresses = some program) :
    ∃ (events : List MemoryAccess) (final : RV.State),
      events.Perm ((unrolledMemory trace workers).steps.map transferEvent) ∧
      events.Pairwise (fun a b => b.1 ≤ a.1) ∧ RVHistory cells events initialState final ∧
      (∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.readRV final = some (memoryWord sink.value)) :=
  shared_history (unrolled_memory_facts accepted initial alignedClock image) image distinct aligned
    (unrolled_zero_rules unrolled accepted initial alignedClock programImage)

/-- The unified CPU and both worker pools share one RV history from the public seed image. -/
theorem unified_shared_history {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} {initialState : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (alignedClock : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (image : initialImageRV initialState cells = some trace.initialMemory)
    (distinct : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (programImage : rvMachineProgramImage .unified initialState addresses = some program) :
    ∃ (events : List MemoryAccess) (final : RV.State),
      events.Perm ((unifiedMemory trace workers).steps.map transferEvent) ∧
      events.Pairwise (fun a b => b.1 ≤ a.1) ∧ RVHistory cells events initialState final ∧
      (∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.readRV final = some (memoryWord sink.value)) :=
  shared_history (unified_memory_facts accepted initial alignedClock image) image distinct aligned
    (unified_zero_rules accepted initial alignedClock programImage)

end Airbender.Trace.Machine.Proofs
