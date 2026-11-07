import Airbender.Proofs.ReducedMachine.NativeJumpDecodedResult
import Airbender.Proofs.ReducedMachine.NativeJumpPorts
import Airbender.Proofs.Trace.Retirement
import Airbender.Proofs.Sail.JumpRetirement

namespace Airbender.ReducedMachine.NativeJumpExecutionProofs
open Native Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification
open Airbender.JumpBranchSlt
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Recover retained constructors from the original public jump projection. -/
theorem encoding {entry : JumpProgramEntry}
    (fields : jumpDecoderFields entry.instruction = some entry.data) :
    ∃ (instruction : Jump.Instruction) (rs1 rd : BitVec 5), entry.instruction = match instruction with
      | .jal imm => .JAL (imm,.Regidx rd) | .jalr imm => .JALR (imm,.Regidx rs1,.Regidx rd) := by
  unfold jumpDecoderFields at fields
  split at fields
  · rename_i imm rd same
    exact ⟨.jal imm,0,rd,same⟩
  · rename_i imm rs1 rd same
    exact ⟨.jalr imm,rs1,rd,same⟩
  · cases fields

/-- A false public family tag recovers the retained original indirect constructor. -/
theorem indirect_encoding {entry : JumpProgramEntry}
    (fields : jumpDecoderFields entry.instruction = some entry.data)
    (indirect : entry.data.family = false) : ∃ args, entry.instruction = .JALR args := by
  obtain ⟨instruction,rs1,rd,encoded⟩ := encoding fields
  cases instruction with
  | jal imm =>
    rw [encoded] at fields
    have family := congrArg (fun data : DecoderData JumpMode => data.family) (Option.some.inj fields)
    change true = entry.data.family at family
    rw [indirect] at family
    cases family
  | jalr imm => exact ⟨_,encoded⟩

/-- Actual native jump effects and original GPR history instantiate unchanged
    retained Sail retirement. Source bounds/alignment and local CSR reads are
    internal obligations for initialized trace composition, not public answers. -/
theorem local_row_execution {w : Nat → ZMod mersenne31Modulus} {entry : JumpProgramEntry}
    {original : State}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (source : entry.SourceWith original jumpDecoderFields) (query : decoderQuery w = entry.query)
    (readBound : (sourceWord w).Bounded) (aligned : (initialPCWord w).lo % 4 = 0)
    {cells : List Cell} (epoch : Nat) {before after : State}
    (history : SailHistory cells (NativeJumpPortProofs.nativeEvents epoch w).reverse before after)
    (isa : ∃ value, before.regs.get? .misa = some value)
    (configuration : entry.data.family = false → before.regs.get? .cur_privilege = some .Machine ∧
      ∃ security, before.regs.get? .mseccfg = some security ∧ SailRV32.Functions._get_Seccfg_MLPE security = 0) :
    ∃ clause, registerClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (initialPCWord w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (finalPCWord w).toBitVec) := by
  obtain ⟨instruction,rs1,rd,encoded⟩ := encoding source.fields
  let data : DecoderData JumpMode := match instruction with
    | .jal imm => ⟨true,0,0,rd,Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),33025,imm.toNat / 4096 % 8⟩
    | .jalr imm => ⟨false,rs1,0,rd,Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),257,0⟩
  have shape : entry.data = data := by
    have fields := source.fields
    rw [encoded] at fields
    cases instruction <;> exact (Option.some.inj fields).symm
  let pc := (initialPCWord w).toBitVec
  let rebased := retiredState before pc
  let finished := retiredState after pc
  let input : Jump.Input := ⟨instruction,sourceWord w,entry.data.immediate,initialPCWord w,.Regidx rs1,.Regidx rd,rebased⟩
  let output : Output := ⟨writtenWord w,finalPCWord w⟩
  have result := NativeJumpResultProofs.decoded_result holds source query readBound aligned
  have history' := Trace.Proofs.retired_state_history history pc
  have observedLink : output.destination.toBitVec = if input.rd = zeroRegister then 0 else input.pc.toBitVec + 4 := by
    have written := result.2.1
    have index : entry.data.rd = rd := by rw [shape]; cases instruction <;> rfl
    rw [index] at written
    change (writtenWord w).toBitVec =
      if (SailRV32.regidx.Regidx rd) = SailRV32.regidx.Regidx 0 then 0 else (initialPCWord w).toBitVec+4
    rw [written]
    by_cases zero : rd = 0
    · have registerZero : SailRV32.regidx.Regidx rd = SailRV32.regidx.Regidx 0 := congrArg SailRV32.regidx.Regidx zero
      simp only [if_pos zero,if_pos registerZero]
      rfl
    · have registerNonzero : SailRV32.regidx.Regidx rd ≠ SailRV32.regidx.Regidx 0 :=
        fun same => zero (SailRV32.regidx.Regidx.inj same)
      simp only [if_neg zero,if_neg registerNonzero]
      exact Word.ofBitVec_roundtrip _
  have calculated : output.pc.toBitVec = if input.instruction.indirect then
      input.base.toBitVec + input.offset.toBitVec &&& 0xfffffffe else input.base.toBitVec + input.offset.toBitVec := by
    have target := congrArg Word.toBitVec result.2.2.2.1
    rw [Word.ofBitVec_roundtrip] at target
    cases instruction <;> simpa [output,input,Jump.Input.base,Jump.Instruction.indirect,JumpMode.target,JumpMode.base,shape,data] using target
  have targetAligned : output.pc.toBitVec.toNat % 4 = 0 := result.2.2.2.2.2
  have extension : input.offset.toBitVec = match input.instruction with
      | .jal imm => SailRV32.Functions.sign_extend (m := 32) imm
      | .jalr imm => SailRV32.Functions.sign_extend (m := 32) imm := by
    change entry.data.immediate.toBitVec = _
    rw [shape]
    cases instruction <;> exact Word.ofBitVec_roundtrip _
  have reads := NativeJumpPortProofs.register_reads epoch holds source.fields query history'
  have sourceRead : input.instruction.indirect = true →
      run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok input.source.toBitVec input.before := by
    intro indirect
    have index : entry.data.rs1 = rs1 := by
      rw [shape]
      cases instruction <;> simp_all [input,data,Jump.Instruction.indirect]
    have read := reads 0
    simpa [index,input,memoryWord,MemoryPort.readCode,WordColumns.code,WordColumns.evaluate,
      importedConstraintsMemoryPorts,sourceWord,source1,Nat.unpair_pair] using read
  have architectural := Trace.Proofs.retired_state_pc before pc
  have isaRead : ∃ value, run (SailRV32.readReg .misa) input.before = .ok value input.before := by
    obtain ⟨value,read⟩ := isa
    refine ⟨value,read_register ?_⟩
    simpa [input,rebased,retiredState,Std.ExtDHashMap.get?_insert] using read
  have landingPad : input.instruction.indirect = true →
      run (SailRV32.readReg .cur_privilege) input.before = .ok .Machine input.before ∧
      ∃ security, run (SailRV32.readReg .mseccfg) input.before = .ok security input.before ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0 := by
    intro indirect
    have mode : entry.data.family = false := by
      rw [shape]
      cases instruction <;> simp_all [input,data,Jump.Instruction.indirect]
    obtain ⟨privilege,security,read,disabled⟩ := configuration mode
    constructor
    · apply read_register
      simpa [input,rebased,retiredState,Std.ExtDHashMap.get?_insert] using privilege
    · refine ⟨security,read_register ?_,disabled⟩
      simpa [input,rebased,retiredState,Std.ExtDHashMap.get?_insert] using read
  obtain ⟨checkedAfter,normal,projection⟩ := retire_jump input output observedLink calculated targetAligned
    extension sourceRead architectural isaRead landingPad
  have actual := NativeJumpPortProofs.register_write epoch holds source.fields query history'
  have nativeWrite : run (SailRV32.Functions.wX_bits (.Regidx rd) output.destination.toBitVec) rebased = .ok () finished := by
    have index : entry.data.rd = rd := by rw [shape]; cases instruction <;> rfl
    simpa [index,memoryWord,MemoryPort.writeCode,WordColumns.code,WordColumns.evaluate,
      importedConstraintsMemoryPorts,output,writtenWord,rdWrite,rdPort,Nat.unpair_pair] using actual
  have projected := Trace.Proofs.projected_step_of_write rd output nativeWrite
  have same := (EStateM.Result.ok.inj (projection.symm.trans projected)).2
  rw [same] at normal
  cases instruction
  · refine ⟨_,by rw [encoded]; rfl,?_⟩
    simpa only [Jump.execution,Jump.instruction,registerClause,Option.get_some,input,output,
      rebased,finished,pc,Trace.Proofs.retired_state_overwrite] using normal
  · refine ⟨_,by rw [encoded]; rfl,?_⟩
    simpa only [Jump.execution,Jump.instruction,registerClause,Option.get_some,input,output,
      rebased,finished,pc,Trace.Proofs.retired_state_overwrite] using normal

end Airbender.ReducedMachine.NativeJumpExecutionProofs
