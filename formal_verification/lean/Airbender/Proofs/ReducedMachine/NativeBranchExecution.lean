import Airbender.Review.Circuits.ReducedMachine.ShiftOperand
import Airbender.Proofs.ReducedMachine.NativeBranchClauseReference
import Airbender.Proofs.ReducedMachine.NativeBranchPC
import Airbender.Proofs.ReducedMachine.NativeBranchPorts
import Airbender.Proofs.Trace.Retirement

namespace Airbender.ReducedMachine.NativeBranchExecutionProofs
open Native Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Actual native branch constraints and derived row history execute the retained
    original BTYPE through normal preparation/retirement. Bounds/alignment/parity
    stay internal. The public Sail configuration must make misa readable. -/
theorem local_row_execution {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    {entry : BranchProgramEntry} (fields : branchDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (leftBound : (sourceWord w).Bounded)
    (rightBound : (registerOperandWord w).Bounded)
    (aligned : (initialPCWord w).lo % 4 = 0) (even : (branchOffsetWord w).lo % 2 = 0)
    {cells : List Cell} (epoch : Nat) {before after : State}
    (history : SailHistory cells (NativeBranchPortProofs.nativeEvents epoch w).reverse before after)
    (isa : ∃ value, before.regs.get? .misa = some value) :
    ∃ clause, registerClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (initialPCWord w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (finalPCWord w).toBitVec) := by
  obtain ⟨opcode,imm,rs1,rs2,encoding⟩ := NativeBranchClauseProofs.encoding fields
  have shape : entry.data = (⟨opcode,rs1,rs2,0,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),70,branchFunct3 opcode⟩ : DecoderData BranchMode) := by
    rw [encoding] at fields
    exact (Option.some.inj fields).symm
  have decoded := NativeBranchDecoderProofs.decoded_fields fields query
  have tagBound : branchFunct3 entry.data.family < mersenne31Modulus := by
    have tags := NativeBranchDecoderProofs.tags entry.data.family
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at tags
    change _ < 2147483647
    omega
  have tag : (w 11).val = branchFunct3 opcode := by
    rw [decoded.funct3,ZMod.val_natCast_of_lt tagBound,shape]
  have tags : (w 11).val ∈ [0,1,4,5,6,7] := by rw [tag]; exact NativeBranchDecoderProofs.tags _
  have offset := NativeBranchDecoderProofs.immediate_word fields query
  have sign : (branchOffsetWord w).toBitVec = SailRV32.Functions.sign_extend (m := 32) imm := by
    rw [offset,shape]
    exact Word.ofBitVec_roundtrip _
  have offsetBound : (branchOffsetWord w).Bounded := by
    rw [offset]
    exact (NativeBranchDecoderProofs.field_bounds fields).1
  have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change initialPCWord w = Word.ofBitVec entry.pc at canonical
  have pcBound : (initialPCWord w).Bounded := by rw [canonical]; exact Word.ofBitVec_bound _
  have routing := NativeBranchFieldProofs.source holds decoded.mask
  have lo := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) routing
  have hi := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) routing
  change w 47 = w 37 at lo
  change w 48 = w 38 at hi
  have operand : operandWord w = registerOperandWord w := by simp [operandWord,registerOperandWord,source2,lo,hi,importedConstraintsMemoryPorts,WordColumns.evaluate]
  have operandBound : (operandWord w).Bounded := by rw [operand]; exact rightBound
  let left := sourceWord w
  let right := registerOperandWord w
  let pc := (initialPCWord w).toBitVec
  let output : Output := ⟨writtenWord w,finalPCWord w⟩
  let rebased := retiredState before pc
  let finished := retiredState after pc
  have history' := Trace.Proofs.retired_state_history history pc
  have result := NativeBranchPCProofs.effects holds decoded.mask tags leftBound operandBound pcBound offsetBound aligned even
  have target : output.pc.toBitVec =
      (if branchCondition (w 11).val left right then pc+(branchOffsetWord w).toBitVec else pc+4) ∧
      output.pc.toBitVec.toNat % 4 = 0 := by
    simpa only [output,operand,left,right,pc] using result.2
  rw [tag,sign,NativeBranchClauseProofs.branch_condition_native opcode left right leftBound rightBound] at target
  let taken := NativeBranchClauseProofs.nativeCondition opcode left.toBitVec right.toBitVec
  have calculated : output.pc.toBitVec = if taken then pc+SailRV32.Functions.sign_extend (m := 32) imm else pc+4 := target.1
  have reads := NativeBranchPortProofs.register_reads epoch holds fields query history'
  have leftRead : run (SailRV32.Functions.rX_bits (.Regidx rs1)) rebased = .ok left.toBitVec rebased := by
    simpa [shape,memoryWord,MemoryPort.readCode,WordColumns.code,WordColumns.evaluate,
      importedConstraintsMemoryPorts,left,sourceWord,source1,Nat.unpair_pair] using reads 0
  have rightRead : run (SailRV32.Functions.rX_bits (.Regidx rs2)) rebased = .ok right.toBitVec rebased := by
    simpa [shape,memoryWord,MemoryPort.readCode,WordColumns.code,WordColumns.evaluate,
      importedConstraintsMemoryPorts,right,registerOperandWord,Nat.unpair_pair] using reads 1
  have architectural := Trace.Proofs.retired_state_pc before pc
  let written : State := { rebased with regs := rebased.regs.insert .nextPC output.pc.toBitVec }
  have isaRebased : ∃ value, rebased.regs.get? .misa = some value := by
    obtain ⟨value,read⟩ := isa
    exact ⟨value,by simpa [rebased,retiredState,Std.ExtDHashMap.get?_insert] using read⟩
  have executed := NativeBranchClauseProofs.clause_of_reads opcode imm rs1 rs2 rebased
    left.toBitVec right.toBitVec pc output.pc.toBitVec leftRead rightRead architectural isaRebased calculated target.2
  have checked : stepSpec rebased (SailRV32.Functions.execute_BTYPE imm (.Regidx rs2) (.Regidx rs1) opcode) zeroRegister output := by
    apply retire_of_effects architectural
    refine ⟨written,executed,?_⟩
    simp only [writeResult,write_zero,freeM_pure_bind]
    rfl
  obtain ⟨checkedAfter,normal,projection⟩ := checked
  have actual := NativeBranchPortProofs.register_write epoch holds fields query history'
  have nativeWrite : run (SailRV32.Functions.wX_bits (.Regidx 0) output.destination.toBitVec) rebased = .ok () finished := by
    simpa [shape,memoryWord,MemoryPort.writeCode,WordColumns.code,WordColumns.evaluate,
      importedConstraintsMemoryPorts,output,writtenWord,rdWrite,rdPort,Nat.unpair_pair] using actual
  have projected := Trace.Proofs.projected_step_of_write 0 output nativeWrite
  have same := (EStateM.Result.ok.inj (projection.symm.trans projected)).2
  rw [same] at normal
  refine ⟨SailRV32.Functions.execute_BTYPE imm (.Regidx rs2) (.Regidx rs1) opcode,by rw [encoding]; rfl,?_⟩
  simpa only [rebased,finished,pc,output,Trace.Proofs.retired_state_overwrite] using normal

end Airbender.ReducedMachine.NativeBranchExecutionProofs
