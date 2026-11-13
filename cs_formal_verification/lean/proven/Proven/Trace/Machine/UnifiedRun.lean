module
public import Proven.Trace.Machine.UnifiedCycle
public import Proven.Trace.Machine.UnifiedDelegateCycle
public import Proven.Trace.Machine.SharedHistory
public import Human.Trace.Machine.Theorems

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs Delegation
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Every accepted unified machine trace is a whole RV run, with loops and matched standard calls. -/
theorem unified_realizes
    {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} {initialState : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (alignedClock : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (image : initialImageRV initialState cells = some trace.initialMemory)
    (distinct : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (programImage : rvMachineProgramImage .unified initialState addresses = some program)
    (setup : trace.rom = UnifiedReduced.Setup.tableRV initialState)
    (tables : workers.standard.setup = modeledSetup Keccak.Controller.rows)
    (start : initialState.pc = trace.initial.word.toBitVec) (noSpecial : NoSpecial5 program)
    (streamPorts : UnifiedStreamPorts trace initialState.input) : RVRealizes trace initialState cells := by
  obtain ⟨events, finalState, permutation, ordered, history, terminalReads⟩ :=
    unified_shared_history accepted initial alignedClock image distinct aligned programImage
  let index := readIndexAt trace.rows Row.clock unifiedIsRead
  have zeroIndex : index (timeOfPair trace.initial.timestamp).value = 0 :=
    read_index_initial trace.rows Row.clock unifiedIsRead _ (fun row member =>
      (cpu_cycle_clock_bounds accepted.constraints accepted.states initial alignedClock member).1)
  apply realizes_of_cycle_steps accepted.constraints accepted.states initial alignedClock ordered history
    (fun event present => unified_event_bounds accepted initial alignedClock event (permutation.mem_iff.mp present))
    terminalReads start index zeroIndex
  intro row member before after past _ current
  have rom := (Delegation.Proofs.rv_history_fields past).2.1
  have clocks := state_clock_inputs (by decide) (by decide) accepted.constraints accepted.states initial alignedClock row member
  have advance : (decodeTimestamp row.assignment row.columns.finalTime).value = row.clock + 4 :=
    ClockLaws.advance (by decide) (by decide) trace.rom row (accepted.constraints row member) clocks.1
  rw [advance] at current
  obtain ⟨entry, present, _, query⟩ := accepted.decoded row member
  obtain ⟨_, _, instruction, decoded, fields⟩ := machine_entry_fetch programImage entry present
  apply unified_cycle accepted initial alignedClock image aligned programImage setup tables
    member present query decoded fields streamPorts permutation ordered current rom
  intro kind decoded fields called
  apply unified_delegate_cycle accepted initial alignedClock image distinct aligned programImage tables called present decoded fields query
  · intro same
    subst kind
    exact noSpecial entry present decoded
  · exact permutation
  · exact current
  · exact rom

end Airbender.Trace.Machine.Proofs
