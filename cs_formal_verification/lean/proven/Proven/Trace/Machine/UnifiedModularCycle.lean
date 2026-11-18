module
public import Proven.Trace.Machine.UnifiedNoncallerFacts
public import Proven.Trace.Machine.UnifiedModularStep
public import Proven.Trace.Machine.ExtraViews
public import Proven.Trace.Machine.ExtraFlags
public import Proven.Trace.Machine.InputLift

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs Delegation
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Every nonzero native unified field-operation cycle executes its fetched RV instruction. -/
theorem unified_modular_cycle {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
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
    (opcode : AddSub.Modular.Opcode) (rs1 rs2 rd : BitVec 5) (nonzero : rd ≠ 0)
    (fields : rvMachineExtraFields .unified (.mop opcode.rvOp rd rs1 rs2) = some entry.data)
    (decoded : RV.decode entry.bits = some (.mop opcode.rvOp rd rs1 rs2))
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
      ((modularData opcode rs1 rs2 rd).mapFamily (fun _ => UnifiedFamily.machine)) :=
    (extra_modular_data nonzero fields).trans (unified_arithmetic_view _)
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
  have bound (k : Fin 3) : (readToken w UnifiedReduced.importedConstraintsMemoryPorts[k]).word.Bounded :=
    facts.reads _ (by fin_cases k <;> simp [Row.ports, CircuitLayout.ports, UnifiedReduced.importedConstraintsMemoryPorts])
  have left : (Word.mk (w 36).val (w 37).val).Bounded := by
    simpa [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code, pairCode,
      UnifiedReduced.importedConstraintsMemoryPorts] using bound 0
  have right : (Word.mk (w 42).val (w 43).val).Bounded := by
    simpa [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code, pairCode,
      UnifiedReduced.importedConstraintsMemoryPorts] using bound 1
  have old : (Word.mk (w 48).val (w 49).val).Bounded := by
    simpa [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code, pairCode,
      UnifiedReduced.importedConstraintsMemoryPorts] using bound 2
  obtain ⟨next, executed, same⟩ := unified_modular_row_step opcode rs1 rs2 rd nonzero facts.core facts.active
    facts.query rfl facts.pc left right old facts.history
  have fetched := fetch_decoded programImage present decoded rom (state := before.setPC entry.pc) rfl
  exact ⟨next, fetched.trans executed, same⟩

end Airbender.Trace.Machine.Proofs
