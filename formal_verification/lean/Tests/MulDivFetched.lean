import Tests.MulDivRegisterChain
import Airbender.Review.Trace.Families.MulDiv.FetchedExecution

namespace Tests.MulDivFetched
open Airbender Arithmetic Trace MulDiv Reference.RiscV.Sail Reference.Sail
open Tests.MulDivInitializedFixture

/-- All sixteen cases start from the actual public state, fetch/decode original
    bytes and reach actual native terminal PC/register values. -/
theorem initialized_execution (op : Operation) (discarded zeroDivisor : Bool) :
    Realizes (StepWith MulDiv.decoderFields registerClause (setup op discarded).program)
      (trace op discarded zeroDivisor) (before op discarded zeroDivisor)
      [.register 0,.register 1,.register 2,.register 3] :=
  (MulDiv.public_execution (program_image op discarded zeroDivisor)
    (public_inputs op discarded zeroDivisor) (accepted op discarded zeroDivisor)
    (decoded op discarded zeroDivisor) Tests.MulDivRegisters.aligned).2

/-- Public endpoint matching derives a bounded terminal PC, rather than taking
    it or an expected final state as an execution premise. -/
theorem terminal_bound (op : Operation) (discarded zeroDivisor : Bool) :
    (trace op discarded zeroDivisor).terminal.word.Bounded :=
  (MulDiv.public_execution (program_image op discarded zeroDivisor)
    (public_inputs op discarded zeroDivisor) (accepted op discarded zeroDivisor)
    (decoded op discarded zeroDivisor) Tests.MulDivRegisters.aligned).1

def expected (op : Operation) (zeroDivisor : Bool) : BitVec 32 :=
  match op with
  | .mul => if zeroDivisor then 0 else 861
  | .mulhu => 0
  | .divu => if zeroDivisor then 4294967295 else 17
  | .remu => if zeroDivisor then 4294967295 else 4

/-- Concrete arithmetic outcomes are obtained from actual terminal reads of the
    complete fetched execution, including x0 discard and unsigned division by zero. -/
theorem initialized_values (op : Operation) (discarded zeroDivisor : Bool) :
    ∃ after,
      Relation.ReflTransGen (StepWith MulDiv.decoderFields registerClause (setup op discarded).program)
        (before op discarded zeroDivisor) after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok (4 : BitVec 32) after ∧
      run (SailRV32.Functions.rX_bits (.Regidx 3)) after =
        .ok (if discarded then 0 else expected op zeroDivisor) after := by
  obtain ⟨after,steps,pc,reads⟩ := initialized_execution op discarded zeroDivisor
  let sink := (trace op discarded zeroDivisor).terminalMemory[3]'(by simp [trace])
  have member : sink ∈ (trace op discarded zeroDivisor).terminalMemory := by
    exact List.getElem_mem (by simp [trace])
  obtain ⟨found,present,address,read⟩ := reads sink member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  · have different : (Cell.register 0).addressCode ≠ sink.address := by rintro h; cases op <;> cases discarded <;> cases zeroDivisor <;> cases h
    exact False.elim (different address)
  · have different : (Cell.register 1).addressCode ≠ sink.address := by rintro h; cases op <;> cases discarded <;> cases zeroDivisor <;> cases h
    exact False.elim (different address)
  · have different : (Cell.register 2).addressCode ≠ sink.address := by rintro h; cases op <;> cases discarded <;> cases zeroDivisor <;> cases h
    exact False.elim (different address)
  · have word : (id sink).word.toBitVec = if discarded then 0 else expected op zeroDivisor := by
      cases op <;> cases discarded <;> cases zeroDivisor <;> decide +kernel
    rw [word] at read
    exact ⟨after,steps,pc,read⟩

/-- Newest-first witness rows compose through real native intermediate states.
    The second original instruction decodes after a genuine first GPR write. -/
theorem alias_execution :
    Realizes (StepWith MulDiv.decoderFields registerClause MulDivRegisterChain.setup.program)
      (MulDivRegisterChain.trace false) MulDivRegisterChain.before
      [.register 0,.register 1,.register 2,.register 3] :=
  (MulDiv.public_execution MulDivRegisterChain.program_image MulDivRegisterChain.public_inputs
    MulDivRegisterChain.accepted (MulDivRegisterChain.decoded false) Tests.MulDivRegisters.aligned).2

/-- Actual complete execution reaches PC eight and both native MUL results. -/
theorem alias_values : ∃ after,
    Relation.ReflTransGen (StepWith MulDiv.decoderFields registerClause MulDivRegisterChain.setup.program)
      MulDivRegisterChain.before after ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok (8 : BitVec 32) after ∧
    run (SailRV32.Functions.rX_bits (.Regidx 1)) after = .ok (861 : BitVec 32) after ∧
    run (SailRV32.Functions.rX_bits (.Regidx 3)) after = .ok (861 : BitVec 32) after := by
  obtain ⟨after,steps,pc,reads⟩ := alias_execution
  have read1 : run (SailRV32.Functions.rX_bits (.Regidx 1)) after = .ok (861 : BitVec 32) after := by
    let sink := (MulDivRegisterChain.trace false).terminalMemory[1]'(by simp [MulDivRegisterChain.trace])
    have member : sink ∈ (MulDivRegisterChain.trace false).terminalMemory :=
      List.getElem_mem (by simp [MulDivRegisterChain.trace])
    obtain ⟨found,present,address,read⟩ := reads sink member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at present
    rcases present with rfl | rfl | rfl | rfl
    · have different : (Cell.register 0).addressCode ≠ sink.address := by decide +kernel
      exact False.elim (different address)
    · have word : (id sink).word.toBitVec = (861 : BitVec 32) := by decide +kernel
      rw [word] at read
      exact read
    · have different : (Cell.register 2).addressCode ≠ sink.address := by decide +kernel
      exact False.elim (different address)
    · have different : (Cell.register 3).addressCode ≠ sink.address := by decide +kernel
      exact False.elim (different address)
  have read3 : run (SailRV32.Functions.rX_bits (.Regidx 3)) after = .ok (861 : BitVec 32) after := by
    let sink := (MulDivRegisterChain.trace false).terminalMemory[3]'(by simp [MulDivRegisterChain.trace])
    have member : sink ∈ (MulDivRegisterChain.trace false).terminalMemory :=
      List.getElem_mem (by simp [MulDivRegisterChain.trace])
    obtain ⟨found,present,address,read⟩ := reads sink member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at present
    rcases present with rfl | rfl | rfl | rfl
    · have different : (Cell.register 0).addressCode ≠ sink.address := by decide +kernel
      exact False.elim (different address)
    · have different : (Cell.register 1).addressCode ≠ sink.address := by decide +kernel
      exact False.elim (different address)
    · have different : (Cell.register 2).addressCode ≠ sink.address := by decide +kernel
      exact False.elim (different address)
    · have word : (id sink).word.toBitVec = (861 : BitVec 32) := by decide +kernel
      rw [word] at read
      exact read
  exact ⟨after,steps,pc,read1,read3⟩

/-- Empty native rows have identical actual endpoint state and memory tokens. -/
def emptyTrace : Data mersenne31Modulus MulDivFamily where
  rows := []
  rom := ()
  initial := (trace .mul false false).initial
  terminal := (trace .mul false false).initial
  initialMemory := (trace .mul false false).initialMemory
  terminalMemory := (trace .mul false false).initialMemory

/-- Empty execution derives terminal PC bounds and terminal reads from public
    initialization alone; no row or expected final-state premise is supplied. -/
theorem empty_execution : emptyTrace.terminal.word.Bounded ∧
    Realizes (StepWith MulDiv.decoderFields registerClause (setup .mul false).program)
      emptyTrace (before .mul false false) [.register 0,.register 1,.register 2,.register 3] := by
  have inputs := public_inputs .mul false false
  have accepted : Accepted emptyTrace := by
    constructor
    · intro row present; simp [emptyTrace] at present
    · intro row present; simp [emptyTrace] at present
    · exact List.Perm.refl _
    · exact List.Perm.refl _
  have decoded : MulDiv.Decoded emptyTrace (setup .mul false) := by
    intro row present; simp [emptyTrace] at present
  exact MulDiv.public_execution (trace := emptyTrace) (program_image .mul false false)
    ⟨inputs.domain,inputs.image,inputs.initial⟩ accepted decoded Tests.MulDivRegisters.aligned

end Tests.MulDivFetched
