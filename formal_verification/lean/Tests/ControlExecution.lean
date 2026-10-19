import Tests.JumpExecution
import Tests.BranchExecution
import Airbender.Review.Trace.Families.JumpBranchSlt.Execution

namespace Tests.ControlExecution
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail

private theorem registers_aligned : ∀ cell ∈ [Cell.register 0,.register 1], cell.Aligned := by
  intro cell member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl <;> simp [Cell.Aligned]

/-- The existing two original-byte jump cases now include actual fetch/decoding,
    complete finite execution and native terminal register reads. -/
theorem jumps (indirect : Bool) (misa : BitVec 32) (security : BitVec 64)
    (disabled : SailRV32.Functions._get_Seccfg_MLPE security = 0) :
    Realizes (StepWith JumpBranchSlt.decoderFields registerClause (JumpExecution.setup indirect).program)
      (JumpExecution.trace indirect) (JumpExecution.initial indirect misa security) [.register 0,.register 1] := by
  have isa : ∃ value, (JumpExecution.initial indirect misa security).regs.get? .misa = some value := by
    refine ⟨misa,?_⟩
    cases indirect <;> simp [JumpExecution.initial,Std.ExtDHashMap.get?_insert]
  have configuration : (∃ row ∈ (JumpExecution.trace indirect).rows, (row.assignment 12).val = 2) →
      (JumpExecution.initial indirect misa security).regs.get? .cur_privilege = some .Machine ∧
      ∃ value, (JumpExecution.initial indirect misa security).regs.get? .mseccfg = some value ∧
        SailRV32.Functions._get_Seccfg_MLPE value = 0 := by
    rintro ⟨row,present,mask⟩
    cases indirect
    · have same : row = ControlHistory.nativeRow false := by simpa [JumpExecution.trace,ControlHistory.trace] using present
      subst row
      exact False.elim ((by decide : (ControlHistory.assignment false 12).val ≠ 2) mask)
    · exact ⟨by simp [JumpExecution.initial,Std.ExtDHashMap.get?_insert],security,
        by simp [JumpExecution.initial],disabled⟩
  have accepted : Accepted (JumpExecution.trace indirect) := by
    cases indirect
    · exact ControlHistory.accepted
    · exact JumpTarget.accepted
  have decoded : JumpBranchSlt.Decoded (JumpExecution.trace indirect) (JumpExecution.setup indirect) := by
    cases indirect
    · exact ControlValues.decoded
    · exact JumpTarget.decoded
  exact (JumpBranchSlt.public_execution (JumpExecution.program_image indirect misa security)
    (JumpExecution.public_inputs indirect misa security) accepted decoded isa configuration registers_aligned).2

/-- All eighteen original branch fixtures now reach actual native terminal
    state through original fetched/decoded Sail execution. -/
theorem branches (misa : BitVec 32) (mode : Branches.Mode) (op : Branches.Op) :
    Realizes (StepWith JumpBranchSlt.decoderFields registerClause Branches.setup.program)
      (Branches.trace mode op) (BranchExecution.publicInitial misa mode op) [.register 0,.register 1,.register 2] := by
  have aligned : ∀ cell ∈ [Cell.register 0,.register 1,.register 2], cell.Aligned := by
    intro cell member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [Cell.Aligned]
  have isa : ∃ value, (BranchExecution.publicInitial misa mode op).regs.get? .misa = some value :=
    ⟨misa,by simp [BranchExecution.publicInitial]⟩
  apply (JumpBranchSlt.public_execution (BranchExecution.program_image misa mode op)
    (BranchExecution.public_inputs misa mode op) (Branches.accepted mode op) (Branches.decoded mode op) isa _ aligned).2
  rintro ⟨row,present,mask⟩
  have same : row = Branches.nativeRow mode op := by simpa [Branches.trace] using present
  subst row
  have different : (Branches.assignment mode op 12).val ≠ 2 := by cases mode <;> cases op <;> decide
  exact False.elim (different mask)

/-- Empty control execution derives terminal matching from the public initial
    state and equality of actual endpoints, without a terminal PC premise. -/
def emptyTrace : Data mersenne31Modulus JumpBranchSltFamily where
  rows := []
  rom := ()
  initial := (ControlHistory.trace false).initial
  terminal := (ControlHistory.trace false).initial
  initialMemory := (ControlHistory.trace false).initialMemory
  terminalMemory := (ControlHistory.trace false).initialMemory

theorem empty_execution (misa : BitVec 32) :
    Realizes (StepWith JumpBranchSlt.decoderFields registerClause JumpBranchSlt.NativeSetup.setup.program)
      emptyTrace (JumpExecution.initial false misa 0) [.register 0,.register 1] := by
  have input := JumpExecution.public_inputs false misa 0
  have accepted : Accepted emptyTrace := by
    constructor
    · intro row present; simp [emptyTrace] at present
    · intro row present; simp [emptyTrace] at present
    · exact List.Perm.refl _
    · exact List.Perm.refl _
  have decoded : JumpBranchSlt.Decoded emptyTrace JumpBranchSlt.NativeSetup.setup := by
    intro row present; simp [emptyTrace] at present
  apply (JumpBranchSlt.public_execution (trace := emptyTrace) (JumpExecution.program_image false misa 0)
    ⟨input.domain,input.image,input.initial⟩ accepted decoded ⟨misa,by simp [JumpExecution.initial]⟩ _ registers_aligned).2
  rintro ⟨row,present,_⟩
  simp [emptyTrace] at present

end Tests.ControlExecution
