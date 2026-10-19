import Airbender.Proofs.Trace.Families.JumpBranchSlt.Targets
import Airbender.Proofs.Trace.Families.JumpBranchSlt.RegisterHistory
import Airbender.Proofs.JumpBranchSlt.Link
import Airbender.Proofs.Trace.ControlFlowCSR
import Airbender.Proofs.Sail.JumpRetirement

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification

/-- Native v2 link/target proofs and actual history instantiate the unchanged
    original jump retirement theorem. Initial CSR data is transported through
    the real prefix; all local values, reads and states are derived. -/
theorem original_jump_step {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace) (decoded : Decoded trace setup)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    {w : Nat → ZMod mersenne31Modulus}
    (configuration : (w 12).val = 2 → initial.regs.get? .cur_privilege = some .Machine ∧
      ∃ security, initial.regs.get? .mseccfg = some security ∧ SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (present : (⟨.jumpBranchSlt,w⟩ : Row mersenne31Modulus JumpBranchSltFamily) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (instruction : Jump.Instruction) (rs1 rd : BitVec 5)
    (encoding : entry.instruction = match instruction with
      | .jal imm => .JAL (imm,.Regidx rd) | .jalr imm => .JALR (imm,.Regidx rs1,.Regidx rd))
    {before after : State} {events : List MemoryAccess}
    (history : SailHistory cells (rowEvents trace.memoryEpoch
      (⟨.jumpBranchSlt,w⟩ : Row mersenne31Modulus JumpBranchSltFamily)).reverse before after)
    (past : SailHistory cells events initial before) :
    run (normalStep (match instruction with
      | .jal imm => SailRV32.Functions.execute_JAL imm (.Regidx rd)
      | .jalr imm => SailRV32.Functions.execute_JALR imm (.Regidx rs1) (.Regidx rd)))
      (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (retiredState after (Word.mk (w 13).val (w 14).val).toBitVec) := by
  let data : DecoderData Unit := match instruction with
    | .jal imm => ⟨(),0,0,rd,Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),1,imm.toNat / 4096 % 8⟩
    | .jalr imm => ⟨(),rs1,0,rd,Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),2,0⟩
  have shape : entry.data = data := by
    rw [encoding] at fields
    cases instruction <;> exact (Option.some.inj fields).symm
  have packed := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) query
  change w 12 = (entry.data.mask : ZMod mersenne31Modulus) at packed
  have mask : (w 12).val = if instruction.indirect then 2 else 1 := by
    rw [packed,shape]
    cases instruction <;> rfl
  have jump : (w 12).val ∈ [1,2] := by rw [mask]; cases instruction <;> simp [Jump.Instruction.indirect]
  let currentPC := (Word.mk (w 0).val (w 1).val).toBitVec
  let rebased := retiredState before currentPC
  let finished := retiredState after currentPC
  let input : Jump.Input := ⟨instruction,⟨(w 22).val,(w 23).val⟩,entry.data.immediate,
    ⟨(w 0).val,(w 1).val⟩,.Regidx rs1,.Regidx rd,rebased⟩
  let output : Output := ⟨⟨(w 38).val,(w 39).val⟩,⟨(w 13).val,(w 14).val⟩⟩
  have history' := Trace.Proofs.retired_state_history history currentPC
  have csrs := Trace.Proofs.sail_history_control_flow_csrs past
  have indices := Trace.Proofs.native_query_indices (by decide : limbBase < mersenne31Modulus) query
  have destination : (w 7).val = rd.toNat := by
    have index := indices.2.2
    change (w 7).val = entry.data.rd.toNat at index
    rw [shape] at index
    cases instruction <;> exact index
  have link := public_jump_link image (accepted.constraints _ present) (decoded _ present) jump
  have observedLink : output.destination.toBitVec =
      if input.rd = zeroRegister then 0 else input.pc.toBitVec + 4 := by
    have zero : rd.toNat = 0 ↔ rd = 0 := by
      constructor
      · intro same
        exact BitVec.eq_of_toNat_eq (by simpa using same)
      · rintro rfl
        rfl
    simpa [input,output,zeroRegister,destination,zero] using link
  have offset := Trace.Proofs.native_query_immediate_word (by decide : limbBase < mersenne31Modulus)
    (decoder_field_bounds fields).1 query
  change Word.mk (w 9).val (w 10).val = entry.data.immediate at offset
  have target := image_jump_targets image inputs accepted decoded _ present jump
  dsimp only at target
  rw [offset] at target
  have calculated : output.pc.toBitVec = if input.instruction.indirect then
      (input.base.toBitVec + input.offset.toBitVec) &&& 0xfffffffe else input.base.toBitVec + input.offset.toBitVec := by
    cases chosen : instruction <;> simpa [input,Jump.Input.base,Jump.Instruction.indirect,mask,chosen] using target.1
  have sign : input.offset.toBitVec = match input.instruction with
      | .jal imm => SailRV32.Functions.sign_extend (m := 32) imm
      | .jalr imm => SailRV32.Functions.sign_extend (m := 32) imm := by
    change entry.data.immediate.toBitVec = _
    rw [shape]
    cases instruction <;> exact Word.ofBitVec_roundtrip _
  have reads := history_register_reads (by decide) trace.memoryEpoch history' query
  have sourceIndex : input.instruction.indirect = true → entry.data.rs1 = rs1 := by
    intro indirect
    rw [shape]
    cases instruction <;> simp_all [input,data,Jump.Instruction.indirect]
  have sourceRead : input.instruction.indirect = true →
      run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok input.source.toBitVec input.before := by
    intro indirect
    have read := reads.1
    rw [sourceIndex indirect] at read
    simpa [memoryWord,MemoryPort.readCode,WordColumns.code,WordColumns.evaluate,
      importedConstraintsMemoryPorts,input,Nat.unpair_pair] using read
  have architectural := Trace.Proofs.retired_state_pc before currentPC
  have isaRead : ∃ value, run (SailRV32.readReg .misa) input.before = .ok value input.before := by
    obtain ⟨value,read⟩ := isa
    refine ⟨value,read_register ?_⟩
    simpa [input,rebased,retiredState,Std.ExtDHashMap.get?_insert] using csrs.1.trans read
  have landingPad : input.instruction.indirect = true →
      run (SailRV32.readReg .cur_privilege) input.before = .ok .Machine input.before ∧
      ∃ security, run (SailRV32.readReg .mseccfg) input.before = .ok security input.before ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0 := by
    intro indirect
    have indirect' : instruction.indirect = true := indirect
    obtain ⟨privilege,security,read,disabled⟩ := configuration (by simpa [indirect'] using mask)
    constructor
    · apply read_register
      simpa [input,rebased,retiredState,Std.ExtDHashMap.get?_insert] using csrs.2.1.trans privilege
    · refine ⟨security,read_register ?_,disabled⟩
      simpa [input,rebased,retiredState,Std.ExtDHashMap.get?_insert] using csrs.2.2.trans read
  obtain ⟨checkedAfter,normal,projection⟩ := retire_jump input output observedLink calculated target.2
    sign sourceRead architectural isaRead landingPad
  have actual := history_register_write (by decide) trace.memoryEpoch history' query
  have nativeWrite : run (SailRV32.Functions.wX_bits (.Regidx rd) output.destination.toBitVec) rebased =
      .ok () finished := by
    have index : entry.data.rd = rd := by rw [shape]; cases instruction <;> rfl
    rw [index] at actual
    simpa [memoryWord,MemoryPort.writeCode,WordColumns.code,WordColumns.evaluate,
      importedConstraintsMemoryPorts,output,Nat.unpair_pair] using actual
  have projected := Trace.Proofs.projected_step_of_write rd output nativeWrite
  have same := (EStateM.Result.ok.inj (projection.symm.trans projected)).2
  rw [same] at normal
  cases instruction <;> simpa only [Jump.execution,Jump.instruction,registerClause,Option.get_some,
    input,output,rebased,finished,Trace.Proofs.retired_state_overwrite] using normal

/-- Exact original constructors are recovered from native jump masks. -/
theorem jump_encoding {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data) (mask : entry.data.mask ∈ [1,2]) :
    ∃ (instruction : Jump.Instruction) (rs1 rd : BitVec 5), entry.instruction = match instruction with
      | .jal imm => .JAL (imm,.Regidx rd) | .jalr imm => .JALR (imm,.Regidx rs1,.Regidx rd) := by
  unfold decoderFields at fields
  split at fields
  all_goals first | (solve | cases fields) | (try (rw [← Option.some.inj fields] at mask; norm_num at mask))
  case h_6 =>
    rename_i _ imm rd encoding
    exact ⟨.jal imm,0,rd,encoding⟩
  case h_7 =>
    rename_i _ imm rs1 rd encoding
    exact ⟨.jalr imm,rs1,rd,encoding⟩

/-- Original public decoding selects JAL/JALR and the checked native row
    executes and retires in its actual initialized-history segment. -/
theorem image_jump_retirement {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace) (decoded : Decoded trace setup)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    {w : Nat → ZMod mersenne31Modulus}
    (configuration : (w 12).val = 2 → initial.regs.get? .cur_privilege = some .Machine ∧
      ∃ security, initial.regs.get? .mseccfg = some security ∧ SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (present : (⟨.jumpBranchSlt,w⟩ : Row mersenne31Modulus JumpBranchSltFamily) ∈ trace.rows)
    (jump : (w 12).val ∈ [1,2])
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) {before after : State} {events : List MemoryAccess}
    (history : SailHistory cells (rowEvents trace.memoryEpoch
      (⟨.jumpBranchSlt,w⟩ : Row mersenne31Modulus JumpBranchSltFamily)).reverse before after)
    (past : SailHistory cells events initial before) :
    ∃ clause, registerClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (Word.mk (w 13).val (w 14).val).toBitVec) := by
  have choices := (decoder_field_bounds fields).2.1
  have small : entry.data.mask < mersenne31Modulus := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at choices
    rcases choices with eq | eq | eq | eq | eq <;> rw [eq] <;> decide
  have packed := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) query
  change w 12 = (entry.data.mask : ZMod mersenne31Modulus) at packed
  have entryMask : entry.data.mask ∈ [1,2] := by
    rwa [packed,ZMod.val_natCast_of_lt small] at jump
  obtain ⟨instruction,rs1,rd,encoding⟩ := jump_encoding fields entryMask
  cases instruction with
  | jal imm =>
    refine ⟨SailRV32.Functions.execute_JAL imm (.Regidx rd),congrArg registerClause encoding,?_⟩
    exact original_jump_step image inputs accepted decoded isa configuration present fields query
      (.jal imm) rs1 rd encoding history past
  | jalr imm =>
    refine ⟨SailRV32.Functions.execute_JALR imm (.Regidx rs1) (.Regidx rd),congrArg registerClause encoding,?_⟩
    exact original_jump_step image inputs accepted decoded isa configuration present fields query
      (.jalr imm) rs1 rd encoding history past

/-- Both original jump clauses retire in their constructed native segments. -/
theorem image_jump_execution {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup)
    (isa : ∃ value, before.regs.get? .misa = some value)
    (configuration : (∃ row ∈ trace.rows, (row.assignment 12).val = 2) →
      before.regs.get? .cur_privilege = some .Machine ∧ ∃ security,
        before.regs.get? .mseccfg = some security ∧ SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList)
      (rows : List (Row mersenne31Modulus JumpBranchSltFamily)) (after : State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) before after ∧
      SailStateMatches cells history after ∧
      ∀ newer row older, rows = newer ++ row :: older → (row.assignment 12).val ∈ [1,2] →
        ∃ entry ∈ setup.program, ∃ rowBefore rowAfter clause,
          entry.SourceWith before decoderFields ∧ row.decoderQuery = entry.query ∧
          SailHistory cells (older.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) before rowBefore ∧
          SailHistory cells (rowEvents trace.memoryEpoch row).reverse rowBefore rowAfter ∧
          SailHistory cells (newer.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) rowAfter after ∧
          registerClause entry.instruction = some clause ∧
          run (normalStep clause)
            (retiredState rowBefore (Word.mk (row.assignment 0).val (row.assignment 1).val).toBitVec) =
            .ok SailRV32.Functions.RETIRE_SUCCESS
              (retiredState rowAfter (Word.mk (row.assignment 13).val (row.assignment 14).val).toBitVec) := by
  obtain ⟨history,rows,after,consistent,permutation,ordered,sail,final,segments⟩ :=
    image_register_history image inputs accepted decoded aligned
  refine ⟨history,rows,after,consistent,permutation,ordered,sail,final,?_⟩
  intro newer row older shape mask
  obtain ⟨entry,member,rowBefore,rowAfter,source,query,earlier,current,later,_⟩ :=
    segments newer row older shape
  have present : row ∈ trace.rows := permutation.mem_iff.mp (by rw [shape]; simp)
  cases row with
  | mk family w =>
    cases family
    rw [row_decoder_query] at query
    obtain ⟨clause,matched,retired⟩ :=
      image_jump_retirement image inputs accepted decoded isa
        (fun indirect => configuration ⟨_,present,indirect⟩) present mask source.fields query current earlier
    exact ⟨entry,member,rowBefore,rowAfter,clause,source,query,earlier,current,later,matched,retired⟩

end Airbender.JumpBranchSlt.Proofs
