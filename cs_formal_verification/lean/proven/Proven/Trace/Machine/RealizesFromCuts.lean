module
public import Proven.Trace.Machine.MemoryCuts
public import Proven.Trace.Machine.HistoryPrefix
public import Proven.ISA.RV.Input
public import Human.Trace.RVExecution

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Rebase a memory cut to its native PC and the unused part of the independent input stream. -/
def nativeView (initial : RV.State) (index : Nat → Nat) (boundary : PCState.State p) (state : RV.State) : RV.State :=
  (state.setPC boundary.word.toBitVec).withInput (initial.input.drop (index (timeOfPair boundary.timestamp).value))

/-- Native CPU path matching and local steps over one shared history imply whole-machine RV realization. -/
theorem realizes_of_cycle_steps {Kind : Type} [CircuitLayout Kind] [ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind} {initial finalState : RV.State} {cells : List Cell} {events : List MemoryAccess}
    (constraints : ∀ row ∈ trace.rows, FlatOperation.ConstraintsHoldFlat
      (Verification.environment row.assignment) (row.constraints trace.rom))
    (states : (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start))
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (alignedClock : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1)) (history : RVHistory cells events initial finalState)
    (bounds : ∀ event ∈ events, (timeOfPair trace.initial.timestamp).value < event.1 ∧
      event.1 ≤ (timeOfPair trace.terminal.timestamp).value)
    (terminal : ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.readRV finalState = some (memoryWord sink.value))
    (start : initial.pc = trace.initial.word.toBitVec) (index : Nat → Nat)
    (firstIndex : index (timeOfPair trace.initial.timestamp).value = 0)
    (steps : ∀ row ∈ trace.rows, ∀ before after,
      CutState cells events initial row.clock before →
      CutState cells events initial (decodeTimestamp row.assignment row.columns.finalTime).value after →
      RVHistory cells (events.filter fun event => decide (row.clock < event.1 ∧
        event.1 ≤ (decodeTimestamp row.assignment row.columns.finalTime).value)) before after →
      ∃ next, RV.step (nativeView initial index row.start before) = some next ∧
        RV.Same next (nativeView initial index row.finish after)) : RVRealizes trace initial cells := by
  obtain ⟨path, properties⟩ := state_path_checks (by decide) (by decide) constraints states initialClock alignedClock
  have endpoints := history_endpoint_cuts history bounds
  let clock := fun state : PCState.State babyBearModulus => (timeOfPair state.timestamp).value
  have transitions : ∀ edge ∈ path.zip path.tail, ∃ one two,
      CutState cells events initial (clock edge.1) one ∧ CutState cells events initial (clock edge.2) two ∧
      ∃ next, RV.step (nativeView initial index edge.1 one) = some next ∧
        RV.Same next (nativeView initial index edge.2 two) := by
    intro edge present
    obtain ⟨row, member, rfl⟩ := List.mem_map.mp (properties.2.2.1.mem_iff.mp present)
    have clocks := state_clock_inputs (by decide) (by decide) constraints states initialClock alignedClock row member
    have advance := ClockLaws.advance (by decide) (by decide) trace.rom row (constraints row member) clocks.1
    have range : row.clock ≤ (decodeTimestamp row.assignment row.columns.finalTime).value := by
      change (decodeTimestamp row.assignment row.columns.finalTime).value = row.clock + 4 at advance
      omega
    obtain ⟨one, two, _, past, current, _⟩ := rv_history_window ordered history range
    have finish := history_prefix_of_window ordered range past current
    exact ⟨one, two, past, finish, steps row member one two past finish current⟩
  obtain ⟨actual, run, same⟩ := compose_cuts clock (nativeView initial index) properties.1 properties.2.1
    endpoints.1 endpoints.2 transitions
  have firstView : nativeView initial index trace.initial initial = initial := by
    simp only [nativeView, firstIndex, List.drop_zero]
    rw [← start]
    cases initial
    rfl
  rw [firstView] at run
  refine ⟨path.length - 1, actual, run, same.1, ?_⟩
  intro sink member
  obtain ⟨cell, present, address, read⟩ := terminal sink member
  refine ⟨cell, present, address, ?_⟩
  rw [readRV_congr_same same]
  cases cell <;> exact read

end Airbender.Trace.Machine.Proofs
