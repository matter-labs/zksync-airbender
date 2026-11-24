module
public import Proven.Trace.Machine.UnifiedProjectedRowFacts
public import Proven.Trace.Machine.OrdinaryFlags
public import Proven.Trace.Machine.CycleGroups
public import Proven.Trace.Machine.MemoryBounds
public import Proven.Trace.Machine.InputLift

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs Delegation
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Each ordinary unified native cycle executes its fetched RV instruction in the shared history. -/
theorem unified_ordinary_cycle {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} {initialState before after : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (alignedClock : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (image : initialImageRV initialState cells = some trace.initialMemory)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (programImage : rvMachineProgramImage .unified initialState addresses = some program)
    (setup : trace.rom = UnifiedReduced.Setup.tableRV initialState)
    (tables : workers.standard.setup = modeledSetup Keccak.Controller.rows)
    {row : Row babyBearModulus UnifiedFamily} (member : row ∈ trace.rows)
    {entry : RVMachineProgramEntry} (present : entry ∈ program)
    {ordinary : DecoderData UnifiedFamily} {instruction : RV.Instr}
    (fields : UnifiedReduced.rvDecoderFields instruction = some ordinary)
    (data : entry.data = RVMachineDecoderData.ofOrdinary (family := fun _ => .unified) ordinary)
    (query : row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    (decoded : RV.decode entry.bits = some instruction)
    {events : List MemoryAccess} (permutation : events.Perm ((unifiedMemory trace workers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : RVHistory cells (events.filter fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)) before after)
    (rom : before.rom = initialState.rom) :
    ∃ next, RV.step (before.setPC entry.pc) = some next ∧ RV.Same next (after.setPC row.finish.word.toBitVec) := by
  obtain ⟨tag, w⟩ := row
  cases tag
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (UnifiedReduced.importedConstraints trace.rom) UnifiedReduced.importedConstraintsTimestampLookups)
  have flags := unified_ordinary_flags core fields data query
  have notCalled : (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily) ∉
      trace.rows.filter (fun source => decide (UnifiedReduced.Caller.Selected source.assignment)) := by
    intro called
    exact flags.1 (of_decide_eq_true (List.mem_filter.mp called).2)
  have ports : UnifiedReduced.Caller.machinePorts (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily) =
      (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).ports := by
    unfold UnifiedReduced.Caller.machinePorts
    exact ite_eq_right flags.1
  have grouped := unified_ordinary_cycle_group accepted initial alignedClock permutation member notCalled
  rw [ports] at grouped
  have clock := state_clock_inputs (by decide) (by decide) accepted.constraints accepted.states initial alignedClock _ member
  have words := (unified_memory_bounds accepted initial alignedClock image tables).1
  have reads : ∀ port ∈ (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).ports,
      (readToken w port).word.Bounded := by
    intro port included
    have step : (readToken w port, writeToken (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).columns w port) ∈
        (unifiedMemory trace workers).steps :=
      List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨⟨.machine, w⟩, member,
        List.mem_map.mpr ⟨port, by simpa [ports] using included, rfl⟩⟩))
    exact (words _ step).1
  have facts := unified_projected_row_facts (trace := trace) (w := w)
    (initial := initialState) (before := before) (after := after) (cells := cells)
    (entry := entry) (ordinary := ordinary) (instruction := instruction)
    programImage present data query (accepted.constraints ⟨.machine, w⟩ member)
    (accepted.active _ member) clock reads aligned setup fields decoded grouped
    (ordered.sublist List.filter_sublist) history rom
  obtain ⟨next, executed, same⟩ := UnifiedReduced.Proofs.RV.row_step (by decide) (by decide) facts
  have fetched := fetch_decoded programImage present decoded rom (state := before.setPC entry.pc) rfl
  exact ⟨next, fetched.trans executed, same⟩

end Airbender.Trace.Machine.Proofs
