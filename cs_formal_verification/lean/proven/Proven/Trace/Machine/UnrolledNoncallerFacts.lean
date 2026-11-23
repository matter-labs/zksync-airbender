module
public import Proven.Trace.Machine.ProjectedRowFacts
public import Proven.Trace.Machine.CycleGroups
public import Proven.Trace.Machine.MemoryBounds
public import Proven.Trace.Machine.PCBounds

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs Delegation
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- A non-caller native cycle supplies register history and bounds for any exact typed metadata view. -/
theorem unrolled_noncaller_facts {config : RVMachineConfig} (unrolled : config ≠ .unified)
    {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} {initialState before after : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (alignedClock : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (image : initialImageRV initialState cells = some trace.initialMemory)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (programImage : rvMachineProgramImage config initialState addresses = some program)
    (wordSetup : trace.rom.wordMemory = ROM.table cells (romImageRV initialState cells))
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initialState))
    (tables : workers.standard.setup = modeledSetup Keccak.Controller.rows) (terminal : trace.terminal.word.Bounded)
    {row : Row babyBearModulus PooledFamily} (member : row ∈ trace.rows)
    (notCalled : row ∉ unrolledCallers trace)
    {entry : RVMachineProgramEntry} (present : entry ∈ program)
    {ordinary : DecoderData PooledFamily}
    (data : entry.data = RVMachineDecoderData.ofOrdinary (family := RVMachineDecoderFamily.pooled) ordinary)
    (family : entry.data.family = .pooled row.family)
    (query : row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    {events : List MemoryAccess} (permutation : events.Perm ((unrolledMemory trace workers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : RVHistory cells (events.filter fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)) before after)
    (rom : before.rom = initialState.rom) :
    RVPooledRowFacts trace initialState cells row (before.setPC entry.pc) (after.setPC entry.pc)
      ⟨entry.pc, entry.bits, ordinary⟩ := by
  have notSelected : (row.family == .addSub && decide (Requests.Selected row.assignment)) ≠ true := by
    intro selected
    exact notCalled (List.mem_filter.mpr ⟨member, selected⟩)
  have ports : Caller.machinePorts row = row.ports := by
    unfold Caller.machinePorts
    exact ite_eq_right notSelected
  have grouped := unrolled_ordinary_cycle_group accepted initial alignedClock permutation member notCalled
  rw [ports] at grouped
  have clock := state_clock_inputs (by decide) (by decide) accepted.constraints accepted.states initial alignedClock row member
  have words := (unrolled_memory_bounds unrolled accepted initial alignedClock image programImage wordSetup subwordSetup tables).1
  have reads : ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded := by
    intro port included
    have step : (readToken row.assignment port, writeToken row.columns row.assignment port) ∈
        (unrolledMemory trace workers).steps :=
      List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨row, member,
        List.mem_map.mpr ⟨port, by simpa [ports] using included, rfl⟩⟩))
    exact (words _ step).1
  have finish := machine_finish_bounds accepted.states (fun source included => by
    obtain ⟨entry, _, _, query⟩ := accepted.decoded source included
    exact ⟨entry, query⟩) terminal row member
  exact unrolled_projected_row_facts (trace := trace) (ordinary := ordinary) programImage present data family query
    (accepted.constraints row member) (accepted.active row member) clock reads finish aligned wordSetup subwordSetup
    grouped (ordered.sublist List.filter_sublist) history rom

end Airbender.Trace.Machine.Proofs
