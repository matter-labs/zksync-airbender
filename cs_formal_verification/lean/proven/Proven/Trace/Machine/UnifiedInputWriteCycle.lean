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

/-- An accepted unified input-write cycle executes the public hint without consuming input. -/
theorem unified_input_write_cycle {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
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
    (source : BitVec 5)
    (fields : rvMachineExtraFields .unified (.inputWrite source) = some entry.data)
    (decoded : RV.decode entry.bits = some (.inputWrite source))
    (query : (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).decoderQuery =
      (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    {events : List MemoryAccess} (permutation : events.Perm ((unifiedMemory trace workers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : RVHistory cells (events.filter fun event => decide
      ((⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).clock < event.1 ∧
        event.1 ≤ (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).clock + 4)) before after)
    (rom : before.rom = initialState.rom) :
    ∃ next, RV.step (before.setPC entry.pc) = some next ∧
      RV.Same next (after.setPC (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).finish.word.toBitVec) := by
  have data : entry.data = RVMachineDecoderData.ofOrdinary (family := fun _ => .unified)
      UnifiedReduced.rvNopFields :=
    (extra_write_data fields).trans (unified_arithmetic_view rvNopData)
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
  obtain ⟨next, executed, same⟩ := unified_input_write_step source facts.core facts.active facts.query rfl facts.pc facts.history
  have fetched := fetch_decoded programImage present decoded rom (state := before.setPC entry.pc) rfl
  exact ⟨next, fetched.trans executed, same⟩

end Airbender.Trace.Machine.Proofs
