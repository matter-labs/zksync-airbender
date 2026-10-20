import Tests.ShiftExecution
import Airbender.Review.Trace.Families.ShiftBinop.FetchedExecution

namespace Tests.ShiftFetched
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false
open Airbender Arithmetic Trace ShiftBinop Reference.RiscV.Sail Reference.Sail
open Tests.ShiftHistoryFixture

/-- All twenty-four complete cases fetch original public bytes, replay original
    stateful decoding and retire to the actual native terminal PC and cells. -/
theorem initialized_execution (sample : Fin 24) :
    Realizes (StepWith ShiftBinop.decoderFields registerClause NativeSetup.setup.program)
      (trace sample) (ShiftValuesFixture.before sample)
      [.register 0,.register 1,.register 2,.register 3] :=
  (ShiftBinop.public_execution (ShiftValuesFixture.program_image sample)
    (ShiftValuesFixture.public_inputs sample) (accepted sample)
    (ShiftValuesFixture.decoded sample) ShiftRegisters.aligned).2

/-- Terminal PC bounds follow from native/public state matching, not a supplied
    terminal range or expected final Sail state. -/
theorem terminal_bound (sample : Fin 24) : (trace sample).terminal.word.Bounded :=
  (ShiftBinop.public_execution (ShiftValuesFixture.program_image sample)
    (ShiftValuesFixture.public_inputs sample) (accepted sample)
    (ShiftValuesFixture.decoded sample) ShiftRegisters.aligned).1

/-- Concrete terminal GPR reads and PC come from the complete original fetched
    execution, retaining signed shifts, sign-extended immediates and x0 discard. -/
theorem initialized_values (sample : Fin 24) :
    ∃ after : State,
      Relation.ReflTransGen (StepWith ShiftBinop.decoderFields registerClause NativeSetup.setup.program)
        (ShiftValuesFixture.before sample) after ∧
      run (SailRV32.Functions.get_arch_pc ()) after =
        .ok (BitVec.ofNat 32 (4 * sample.val + 4)) after ∧
      run (SailRV32.Functions.rX_bits (.Regidx 3)) after =
        .ok (BitVec.ofNat 32 (if sample.val < 12 then ShiftResults.expected[sample.val % 12] else 0)) after := by
  obtain ⟨after,steps,pc,reads⟩ := initialized_execution sample
  let sink := (trace sample).terminalMemory[3]'(by simp [trace])
  have member : sink ∈ (trace sample).terminalMemory := List.getElem_mem (by simp [trace])
  obtain ⟨found,present,address,read⟩ := reads sink member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  · have different : (Cell.register 0).addressCode ≠ sink.address := by fin_cases sample <;> decide +kernel
    exact False.elim (different address)
  · have different : (Cell.register 1).addressCode ≠ sink.address := by fin_cases sample <;> decide +kernel
    exact False.elim (different address)
  · have different : (Cell.register 2).addressCode ≠ sink.address := by fin_cases sample <;> decide +kernel
    exact False.elim (different address)
  · have word : (id sink).word.toBitVec =
        BitVec.ofNat 32 (if sample.val < 12 then ShiftResults.expected[sample.val % 12] else 0) := by
      fin_cases sample <;> decide +kernel
    have endpoint : (trace sample).terminal.word.toBitVec = BitVec.ofNat 32 (4 * sample.val + 4) := by
      fin_cases sample <;> rfl
    rw [word] at read
    rw [endpoint] at pc
    exact ⟨after,steps,pc,read⟩

/-- Empty native executions preserve actual endpoint state and memory tokens. -/
def emptyTrace (sample : Fin 24) : Data mersenne31Modulus ShiftBinopFamily where
  rows := []
  rom := ()
  initial := (trace sample).initial
  terminal := (trace sample).initial
  initialMemory := (trace sample).initialMemory
  terminalMemory := (trace sample).initialMemory

/-- Public initialization alone derives empty execution, terminal bounds and
    actual terminal reads; no local step or desired final state is supplied. -/
theorem empty_execution (sample : Fin 24) : (emptyTrace sample).terminal.word.Bounded ∧
    Realizes (StepWith ShiftBinop.decoderFields registerClause NativeSetup.setup.program)
      (emptyTrace sample) (ShiftValuesFixture.before sample)
      [.register 0,.register 1,.register 2,.register 3] := by
  have inputs := ShiftValuesFixture.public_inputs sample
  have accepted : Accepted (emptyTrace sample) := by
    constructor
    · intro row present; simp [emptyTrace] at present
    · intro row present; simp [emptyTrace] at present
    · exact List.Perm.refl _
    · exact List.Perm.refl _
  have decoded : ShiftBinop.Decoded (emptyTrace sample) NativeSetup.setup := by
    intro row present; simp [emptyTrace] at present
  exact ShiftBinop.public_execution (trace := emptyTrace sample) (ShiftValuesFixture.program_image sample)
    ⟨inputs.domain,inputs.image,inputs.initial⟩ accepted decoded ShiftRegisters.aligned

end Tests.ShiftFetched
