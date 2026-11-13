module
public import Proven.Trace.Machine.UnrolledNoncallerFacts
public import Proven.Trace.Machine.InputRowStep
public import Proven.Trace.Machine.InputIndex
public import Proven.Trace.Machine.ExtraViews
public import Proven.Trace.Machine.ExtraFlags

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs Delegation
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- An accepted native input-read cycle consumes its unique independently supplied response. -/
theorem unrolled_input_read_cycle {config : RVMachineConfig} (unrolled : config ≠ .unified)
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
    {w : Nat → ZMod babyBearModulus} (member : (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily) ∈ trace.rows)
    {entry : RVMachineProgramEntry} (present : entry ∈ program)
    (rd : BitVec 5)
    (fields : rvMachineExtraFields config (.inputRead rd) = some entry.data)
    (decoded : RV.decode entry.bits = some (.inputRead rd))
    (streamPorts : NonDeterminism.Pooled.StreamPorts trace initialState.input)
    (query : (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).decoderQuery =
      (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    {events : List MemoryAccess} (permutation : events.Perm ((unrolledMemory trace workers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : RVHistory cells (events.filter fun event => decide
      ((⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).clock < event.1 ∧
        event.1 ≤ (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).clock + 4)) before after)
    (rom : before.rom = initialState.rom) :
    ∃ next, RV.step ((before.setPC entry.pc).withInput
        (initialState.input.drop (readIndexAt trace.rows Row.clock NonDeterminism.Pooled.isRead
          (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).clock))) = some next ∧
      RV.Same next ((after.setPC (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).finish.word.toBitVec).withInput
        (initialState.input.drop (readIndexAt trace.rows Row.clock NonDeterminism.Pooled.isRead
          (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).clock + 1))) := by
  have data : entry.data = RVMachineDecoderData.ofOrdinary (family := RVMachineDecoderFamily.pooled)
      ((rvReadData rd).mapFamily pooledArithmeticFamily) :=
    (extra_read_data fields).2.trans (unrolled_arithmetic_view unrolled (rvReadData rd) rfl)
  have family : entry.data.family = .pooled .addSub := by rw [data]; rfl
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
  have flags := unrolled_extra_flags core fields query
  have notSelected : ¬ Requests.Selected w := by
    intro selected
    have bad : true = false := by
      simpa only [decide_eq_true selected, isCallerInstruction] using flags.1
    cases bad
  have notCalled : (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily) ∉ unrolledCallers trace := by
    intro called
    have selected : decide (Requests.Selected w) = true := by simpa using (List.mem_filter.mp called).2
    exact notSelected (of_decide_eq_true selected)
  have reading : NonDeterminism.Pooled.isRead (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily) = true := by
    simpa only [RV.Instr.readsInput] using flags.2
  let index := readIndexAt trace.rows Row.clock NonDeterminism.Pooled.isRead
    (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).clock
  have value := streamPorts _ member reading
  change initialState.input[index]? = some (Word.mk (w 33).val (w 34).val).toBitVec at value
  obtain ⟨bound, word⟩ := List.getElem?_eq_some_iff.mp value
  have head : initialState.input.drop index = (Word.mk (w 33).val (w 34).val).toBitVec :: initialState.input.drop (index + 1) := by
    rw [List.drop_eq_getElem_cons bound, word]
  have facts := unrolled_noncaller_facts unrolled accepted initial alignedClock image aligned programImage wordSetup
    subwordSetup tables terminal member notCalled present data family query permutation ordered history rom
  obtain ⟨next, executed, same⟩ := unrolled_input_read_step rd facts rfl
    (initialState.input.drop index) (initialState.input.drop (index + 1)) head
  have fetched := fetch_decoded programImage present decoded rom
    (state := (before.setPC entry.pc).withInput (initialState.input.drop index)) rfl
  exact ⟨next, fetched.trans executed, same⟩

end Airbender.Trace.Machine.Proofs
