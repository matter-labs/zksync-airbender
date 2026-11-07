import Airbender.Review.Trace.Families.ReducedMachine.JumpFetchedExecution

namespace Tests.NativeReducedJumpConfiguration
open Airbender Arithmetic Trace ReducedMachine Native Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private def direct : JumpProgramEntry :=
  ⟨0,0x0080006f,.JAL (8,.Regidx 0),⟨true,0,0,0,⟨8,0⟩,33025,0⟩⟩
private def indirect : JumpProgramEntry :=
  ⟨4,0x008080e7,.JALR (8,.Regidx 1,.Regidx 1),⟨false,1,0,1,⟨8,0⟩,257,0⟩⟩
private def directSetup : SparseDecoderSetup JumpMode := ⟨[some direct],1⟩
private def indirectSetup : SparseDecoderSetup JumpMode := ⟨[some indirect],1⟩
private def configured (misa : BitVec 32) : State :=
  { (default : State) with regs := ((Std.ExtDHashMap.emptyWithCapacity.insert SailRV32.Register.misa misa).insert .cur_privilege .Machine).insert .mseccfg (0 : BitVec 64) }
private def misaOnly (misa : BitVec 32) : State :=
  { (default : State) with regs := Std.ExtDHashMap.emptyWithCapacity.insert SailRV32.Register.misa misa }

/-- The original program keeps raw x0 and aliased JALR operands at native masks. -/
theorem original_fields : jumpDecoderFields direct.instruction = some direct.data ∧
    jumpDecoderFields indirect.instruction = some indirect.data := ⟨rfl,rfl⟩

/-- The public boundary permits every readable misa value; no expected ISA word. -/
theorem unrestricted_misa (misa : BitVec 32) : JumpISA indirectSetup (configured misa) := by
  constructor
  · intro _
    exact ⟨misa,by simp [configured,Std.ExtDHashMap.get?_insert]⟩
  · intro _
    exact ⟨by simp [configured,Std.ExtDHashMap.get?_insert],0,by simp [configured],by decide +kernel⟩

/-- JAL requires no privilege/security read merely because JALR is supported. -/
theorem direct_without_security (misa : BitVec 32) : JumpISA directSetup (misaOnly misa) := by
  constructor
  · intro _
    exact ⟨misa,by simp [misaOnly]⟩
  · rintro ⟨entry,member,args,encoded⟩
    simp [directSetup,SparseDecoderSetup.program] at member
    subst entry
    cases encoded

/-- A nonempty original jump program cannot silently fabricate a missing CSR. -/
theorem missing_misa_rejected : ¬ JumpISA indirectSetup { (default : State) with regs := Std.ExtDHashMap.emptyWithCapacity } := by
  intro isa
  obtain ⟨value,read⟩ := isa.1 (by simp [indirectSetup,SparseDecoderSetup.program])
  simp at read

/-- The original JALR landing-pad read is retained in the public configuration. -/
theorem missing_security_rejected : ¬ JumpISA indirectSetup (misaOnly 0) := by
  intro isa
  obtain ⟨privilege,security,read,_⟩ := isa.2 ⟨indirect,by simp [indirectSetup,SparseDecoderSetup.program],_,rfl⟩
  simp [misaOnly,Std.ExtDHashMap.get?_insert] at read

end Tests.NativeReducedJumpConfiguration
