module
public import Proven.Trace.Machine.UnifiedNoncallerFacts
public import Proven.Trace.Machine.InputRowStep
public import Proven.Trace.Machine.InputIndex
public import Proven.Trace.Machine.ExtraViews
public import Proven.Trace.Machine.ExtraFlags

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs Delegation
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- An accepted unified input-read cycle consumes its unique independently supplied response. -/
theorem unified_input_read_cycle {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} {initialState before after : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (alignedClock : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (image : initialImageRV initialState cells = some trace.initialMemory)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (programImage : rvMachineProgramImage .unified initialState addresses = some program)
    (tables : workers.standard.setup = modeledSetup Keccak.Controller.rows)
    {w : Nat → ZMod babyBearModulus} (member : (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily) ∈ trace.rows)
    {entry : RVMachineProgramEntry} (present : entry ∈ program)
    (rd : BitVec 5)
    (fields : rvMachineExtraFields .unified (.inputRead rd) = some entry.data)
    (decoded : RV.decode entry.bits = some (.inputRead rd))
    (streamPorts : UnifiedStreamPorts trace initialState.input)
    (query : (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).decoderQuery =
      (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    {events : List MemoryAccess} (permutation : events.Perm ((unifiedMemory trace workers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : RVHistory cells (events.filter fun event => decide
      ((⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).clock < event.1 ∧
        event.1 ≤ (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).clock + 4)) before after)
    (rom : before.rom = initialState.rom) :
    ∃ next, RV.step ((before.setPC entry.pc).withInput
        (initialState.input.drop (readIndexAt trace.rows Row.clock unifiedIsRead
          (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).clock))) = some next ∧
      RV.Same next ((after.setPC (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).finish.word.toBitVec).withInput
        (initialState.input.drop (readIndexAt trace.rows Row.clock unifiedIsRead
          (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).clock + 1))) := by
  have data : entry.data = RVMachineDecoderData.ofOrdinary (family := fun _ => .unified)
      ((rvReadData rd).mapFamily (fun _ => UnifiedFamily.machine)) :=
    (extra_read_data fields).2.trans (unified_arithmetic_view (rvReadData rd))
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (UnifiedReduced.importedConstraints trace.rom) UnifiedReduced.importedConstraintsTimestampLookups)
  have flags := unified_extra_flags core fields query
  have notCaller : ¬ UnifiedReduced.Caller.Selected w := by
    intro selected
    have bad : true = false := by
      simpa only [decide_eq_true selected, isCallerInstruction] using flags.1
    cases bad
  have facts := unified_noncaller_facts accepted initial alignedClock image aligned programImage tables member
    notCaller present data query permutation ordered history rom
  have reading : unifiedIsRead (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily) = true := by
    simpa only [RV.Instr.readsInput] using flags.2
  let index := readIndexAt trace.rows Row.clock unifiedIsRead
    (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).clock
  have value := streamPorts _ member reading
  have response : unifiedResponse (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily) =
      (Word.mk (w 50).val (w 51).val).toBitVec := by
    simp [unifiedResponse, UnifiedReduced.Caller.destinationToken, writeToken, MemoryToken.word,
      MemoryPort.writeCode, WordColumns.code, UnifiedReduced.importedConstraintsMemoryPorts]
  rw [response] at value
  change initialState.input[index]? = some (Word.mk (w 50).val (w 51).val).toBitVec at value
  obtain ⟨bound, word⟩ := List.getElem?_eq_some_iff.mp value
  have head : initialState.input.drop index = (Word.mk (w 50).val (w 51).val).toBitVec :: initialState.input.drop (index + 1) := by
    rw [List.drop_eq_getElem_cons bound, word]
  obtain ⟨next, executed, same⟩ := unified_input_read_step rd facts.core facts.active facts.query rfl facts.pc facts.history
    (initialState.input.drop index) (initialState.input.drop (index + 1)) head
  have fetched := fetch_decoded programImage present decoded rom
    (state := (before.setPC entry.pc).withInput (initialState.input.drop index)) rfl
  exact ⟨next, fetched.trans executed, same⟩

end Airbender.Trace.Machine.Proofs
