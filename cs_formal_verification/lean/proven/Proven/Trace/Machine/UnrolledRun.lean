module
public import Proven.Trace.Machine.UnrolledCycle
public import Proven.Trace.Machine.UnrolledDelegateCycle
public import Proven.Trace.Machine.SharedHistory
public import Human.Trace.Machine.Theorems

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs Delegation
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Every accepted unrolled machine trace is a whole RV run, with loops and matched standard or split calls. -/
theorem unrolled_realizes {config : RVMachineConfig} (unrolled : config ≠ .unified)
    {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} {initialState : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (alignedClock : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (image : initialImageRV initialState cells = some trace.initialMemory)
    (distinct : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (programImage : rvMachineProgramImage config initialState addresses = some program)
    (wordSetup : trace.rom.wordMemory = ROM.table cells (romImageRV initialState cells))
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initialState))
    (tables : workers.standard.setup = modeledSetup Keccak.Controller.rows) (terminal : trace.terminal.word.Bounded)
    (start : initialState.pc = trace.initial.word.toBitVec) (noSpecial : NoSpecial5 program)
    (streamPorts : NonDeterminism.Pooled.StreamPorts trace initialState.input) : RVRealizes trace initialState cells := by
  obtain ⟨events, finalState, permutation, ordered, history, terminalReads⟩ :=
    unrolled_shared_history unrolled accepted initial alignedClock image distinct aligned programImage
  let index := readIndexAt trace.rows Row.clock NonDeterminism.Pooled.isRead
  have zeroIndex : index (timeOfPair trace.initial.timestamp).value = 0 :=
    read_index_initial trace.rows Row.clock NonDeterminism.Pooled.isRead _ (fun row member =>
      (cpu_cycle_clock_bounds accepted.constraints accepted.states initial alignedClock member).1)
  apply realizes_of_cycle_steps accepted.constraints accepted.states initial alignedClock ordered history
    (fun event present => unrolled_event_bounds accepted initial alignedClock event (permutation.mem_iff.mp present))
    terminalReads start index zeroIndex
  intro row member before after past _ current
  have rom := (Delegation.Proofs.rv_history_fields past).2.1
  have clocks := state_clock_inputs (by decide) (by decide) accepted.constraints accepted.states initial alignedClock row member
  have advance : (decodeTimestamp row.assignment row.columns.finalTime).value = row.clock + 4 :=
    ClockLaws.advance (by decide) (by decide) trace.rom row (accepted.constraints row member) clocks.1
  rw [advance] at current
  obtain ⟨entry, present, family, query⟩ := accepted.decoded row member
  obtain ⟨_, _, instruction, decoded, fields⟩ := machine_entry_fetch programImage entry present
  apply unrolled_cycle unrolled accepted initial alignedClock image aligned programImage wordSetup subwordSetup tables
    terminal member present family query decoded fields streamPorts permutation ordered current rom
  intro kind decoded fields called
  apply unrolled_delegate_cycle unrolled accepted initial alignedClock image distinct aligned programImage wordSetup
    subwordSetup tables called present decoded fields query
  · intro same
    subst kind
    exact noSpecial entry present decoded
  · exact permutation
  · exact current
  · exact rom

end Airbender.Trace.Machine.Proofs
