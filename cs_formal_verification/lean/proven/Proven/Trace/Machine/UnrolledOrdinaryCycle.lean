module
public import Proven.Trace.Machine.ProjectedRowFacts
public import Proven.Trace.Machine.OrdinaryFlags
public import Proven.Trace.Machine.CycleGroups
public import Proven.Trace.Machine.MemoryBounds
public import Proven.Trace.Machine.PCBounds
public import Proven.Trace.Machine.InputLift

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs Delegation
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Each ordinary unrolled native cycle executes its fetched RV instruction in the shared history. -/
theorem unrolled_ordinary_cycle {config : RVMachineConfig} (unrolled : config ≠ .unified)
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
    {entry : RVMachineProgramEntry} (present : entry ∈ program)
    {ordinary : DecoderData PooledFamily} {instruction : RV.Instr}
    (fields : rvPooledDecoderFields instruction = some ordinary)
    (data : entry.data = RVMachineDecoderData.ofOrdinary (family := RVMachineDecoderFamily.pooled) ordinary)
    (family : entry.data.family = .pooled row.family)
    (query : row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    (decoded : RV.decode entry.bits = some instruction)
    {events : List MemoryAccess} (permutation : events.Perm ((unrolledMemory trace workers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : RVHistory cells (events.filter fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)) before after)
    (rom : before.rom = initialState.rom) :
    ∃ next, RV.step (before.setPC entry.pc) = some next ∧ RV.Same next (after.setPC row.finish.word.toBitVec) := by
  have flags := unrolled_ordinary_flags (accepted.constraints row member) fields data family query
  have notCalled : row ∉ unrolledCallers trace := by
    intro called
    exact flags.1 (List.mem_filter.mp called).2
  have ports : Caller.machinePorts row = row.ports := by
    unfold Caller.machinePorts
    exact ite_eq_right flags.1
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
  have facts := unrolled_projected_row_facts programImage present data family query
    (accepted.constraints row member) (accepted.active row member) clock reads finish aligned wordSetup subwordSetup
    grouped (ordered.sublist List.filter_sublist) history rom
  obtain ⟨next, executed, same⟩ := rv_pooled_row_step (by decide) (by decide) facts fields decoded
  have fetched := fetch_decoded programImage present decoded rom (state := before.setPC entry.pc) rfl
  exact ⟨next, fetched.trans executed, same⟩

end Airbender.Trace.Machine.Proofs
