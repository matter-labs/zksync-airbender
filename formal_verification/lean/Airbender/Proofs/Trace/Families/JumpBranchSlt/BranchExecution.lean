import Airbender.Proofs.Trace.Families.JumpBranchSlt.BranchTargets
import Airbender.Proofs.Trace.Families.JumpBranchSlt.RegisterHistory
import Airbender.Proofs.Trace.ControlFlowCSR
import Airbender.Proofs.Sail.ControlFlow

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification

/-- The pure comparison appearing inside the generated execute_BTYPE clause. -/
private def nativeCondition (op : SailRV32.bop) (left right : BitVec 32) : Bool :=
  match op with
  | .BEQ => left == right | .BNE => left != right
  | .BLT => SailRV32.Functions.zopz0zI_s left right
  | .BGE => SailRV32.Functions.zopz0zKzJ_s left right
  | .BLTU => SailRV32.Functions.zopz0zI_u left right
  | .BGEU => SailRV32.Functions.zopz0zKzJ_u left right

/-- The six native predicates agree with the pure comparisons in original Sail. -/
theorem branch_condition_native (opcode : SailRV32.bop) (left right : Word)
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    branchCondition (Branch.funct3 opcode) left right = nativeCondition opcode left.toBitVec right.toBitVec := by
  cases opcode <;> simp [branchCondition,Branch.funct3,nativeCondition,
    SailRV32.Functions.zopz0zI_s,SailRV32.Functions.zopz0zKzJ_s,
    SailRV32.Functions.zopz0zI_u,SailRV32.Functions.zopz0zKzJ_u,_root_.Sail.BitVec.toNatInt,
    Word.toBitVec_toNat leftBound,Word.toBitVec_toNat rightBound]
  all_goals by_cases same : left.toBitVec = right.toBitVec <;> simp_all

/-- Original branch execution and retirement derive from native conditions,
    targets and actual same-pre-state reads. The public ISA CSR is transported
    through the real history, without a per-row read/result/PC interface. -/
theorem original_branch_step {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace) (decoded : Decoded trace setup)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    {w : Nat → ZMod mersenne31Modulus}
    (present : (⟨.jumpBranchSlt,w⟩ : Row mersenne31Modulus JumpBranchSltFamily) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (opcode : SailRV32.bop) (imm : BitVec 13) (rs1 rs2 : BitVec 5)
    (encoding : entry.instruction = .BTYPE (imm,.Regidx rs2,.Regidx rs1,opcode))
    {before after : State} {events : List MemoryAccess}
    (history : SailHistory cells (rowEvents trace.memoryEpoch
      (⟨.jumpBranchSlt,w⟩ : Row mersenne31Modulus JumpBranchSltFamily)).reverse before after)
    (past : SailHistory cells events initial before) :
    run (normalStep (SailRV32.Functions.execute_BTYPE imm (.Regidx rs2) (.Regidx rs1) opcode))
      (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (retiredState after (Word.mk (w 13).val (w 14).val).toBitVec) := by
  have shape : entry.data = (⟨(),rs1,rs2,0,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),16,Branch.funct3 opcode⟩ : DecoderData Unit) := by
    rw [encoding] at fields
    exact (Option.some.inj fields).symm
  have packed := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) query
  change w 12 = (entry.data.mask : ZMod mersenne31Modulus) at packed
  have mask : (w 12).val = 16 := by
    rw [packed,shape]
    change (16 : ZMod mersenne31Modulus).val = 16
    decide
  have tag := query_tag (by decide) fields query
  rw [shape] at tag
  have offset := Trace.Proofs.native_query_immediate_word (by decide : limbBase < mersenne31Modulus)
    (decoder_field_bounds fields).1 query
  change Word.mk (w 9).val (w 10).val = entry.data.immediate at offset
  have sign : (Word.mk (w 9).val (w 10).val).toBitVec =
      SailRV32.Functions.sign_extend (m := 32) imm := by
    rw [offset,shape]
    exact Word.ofBitVec_roundtrip _
  let left : Word := ⟨(w 22).val,(w 23).val⟩
  let right : Word := ⟨(w 24).val,(w 25).val⟩
  let pc := (Word.mk (w 0).val (w 1).val).toBitVec
  let output : Output := ⟨⟨(w 38).val,(w 39).val⟩,⟨(w 13).val,(w 14).val⟩⟩
  let rebased := retiredState before pc
  let finished := retiredState after pc
  have history' := Trace.Proofs.retired_state_history history pc
  have values := image_value_bounds image inputs accepted decoded
  have readBounds (i : Fin 2) : (readToken w importedConstraintsMemoryPorts[i.val]).word.Bounded :=
    values.1 ⟨.jumpBranchSlt,w⟩ present _ (by
      change importedConstraintsMemoryPorts[i.val] ∈ importedConstraintsMemoryPorts
      fin_cases i <;> simp [importedConstraintsMemoryPorts])
  have leftBound : left.Bounded := by
    have bound := readBounds ⟨0,by decide⟩
    rw [Trace.Proofs.read_word] at bound
    exact bound
  have rightBound : right.Bounded := by
    have bound := readBounds ⟨1,by decide⟩
    rw [Trace.Proofs.read_word] at bound
    exact bound
  have target := image_branch_targets image inputs accepted decoded _ present mask
  change output.pc.toBitVec =
    (if branchCondition (w 11).val left right then pc + (Word.mk (w 9).val (w 10).val).toBitVec else pc + 4) ∧
    output.pc.toBitVec.toNat % 4 = 0 at target
  rw [tag,sign,branch_condition_native opcode left right leftBound rightBound] at target
  let taken := nativeCondition opcode left.toBitVec right.toBitVec
  have calculated : output.pc.toBitVec =
      if taken then pc + SailRV32.Functions.sign_extend (m := 32) imm else pc + 4 := target.1
  have reads := history_register_reads (by decide) trace.memoryEpoch history' query
  have leftRead : run (SailRV32.Functions.rX_bits (.Regidx rs1)) rebased = .ok left.toBitVec rebased := by
    simpa [shape,memoryWord,MemoryPort.readCode,WordColumns.code,WordColumns.evaluate,
      importedConstraintsMemoryPorts,left,Nat.unpair_pair] using reads.1
  have rightRead : run (SailRV32.Functions.rX_bits (.Regidx rs2)) rebased = .ok right.toBitVec rebased := by
    simpa [shape,memoryWord,MemoryPort.readCode,WordColumns.code,WordColumns.evaluate,
      importedConstraintsMemoryPorts,right,Nat.unpair_pair] using reads.2
  have architectural := Trace.Proofs.retired_state_pc before pc
  have leftPrepared := rX_nextPC (pc := pc + 4) (.Regidx rs1) leftRead
  have rightPrepared := rX_nextPC (pc := pc + 4) (.Regidx rs2) rightRead
  have pcPrepared := read_register_nextPC (pc + 4) (by decide)
    (show run (SailRV32.readReg .PC) rebased = .ok pc rebased from architectural)
  let prepared : State := { rebased with regs := rebased.regs.insert .nextPC (pc + 4) }
  let written : State := { rebased with regs := rebased.regs.insert .nextPC output.pc.toBitVec }
  have reduced : run (SailRV32.Functions.execute_BTYPE imm (.Regidx rs2) (.Regidx rs1) opcode) prepared =
      run (if taken then SailRV32.Functions.jump_to (pc + SailRV32.Functions.sign_extend (m := 32) imm)
        else pure SailRV32.Functions.RETIRE_SUCCESS) prepared := by
    cases op : opcode <;> simp only [SailRV32.Functions.execute_BTYPE,freeM_bind_assoc,freeM_pure_bind]
    all_goals rw [run_bind_of_ok _ _ _ _ _ leftPrepared,run_bind_of_ok _ _ _ _ _ rightPrepared]
    all_goals simp only [taken,nativeCondition,op]
    all_goals split
    all_goals first | (rw [run_bind_of_ok _ _ _ _ _ pcPrepared]) | rfl
  have executed : run (SailRV32.Functions.execute_BTYPE imm (.Regidx rs2) (.Regidx rs1) opcode) prepared =
      .ok SailRV32.Functions.RETIRE_SUCCESS written := by
    rw [reduced]
    cases condition : taken
    · simp only [condition,Bool.false_eq_true,if_false] at calculated ⊢
      simp only [prepared,written,calculated]
      rfl
    · simp only [condition,if_true] at calculated ⊢
      obtain ⟨misa,read⟩ := isa
      have csrs := Trace.Proofs.sail_history_control_flow_csrs past
      have readable : run (SailRV32.readReg .misa) rebased = .ok misa rebased := by
        apply read_register
        simpa [rebased,retiredState,Std.ExtDHashMap.get?_insert] using csrs.1.trans read
      have read' := read_register_nextPC (pc + 4) (by decide) readable
      rw [← calculated]
      simpa only [prepared,written,nextPC_overwrite] using jump_to_aligned target.2 read'
  have checked : stepSpec rebased
      (SailRV32.Functions.execute_BTYPE imm (.Regidx rs2) (.Regidx rs1) opcode) zeroRegister output := by
    apply retire_of_effects architectural
    refine ⟨written,executed,?_⟩
    simp only [writeResult,write_zero,freeM_pure_bind]
    rfl
  obtain ⟨checkedAfter,normal,projection⟩ := checked
  have actual := history_register_write (by decide) trace.memoryEpoch history' query
  have nativeWrite : run (SailRV32.Functions.wX_bits (.Regidx 0) output.destination.toBitVec) rebased =
      .ok () finished := by
    simpa [shape,memoryWord,MemoryPort.writeCode,WordColumns.code,WordColumns.evaluate,
      importedConstraintsMemoryPorts,output,Nat.unpair_pair] using actual
  have projected := Trace.Proofs.projected_step_of_write 0 output nativeWrite
  have same := (EStateM.Result.ok.inj (projection.symm.trans projected)).2
  rw [same] at normal
  simpa only [rebased,finished,Trace.Proofs.retired_state_overwrite] using normal

/-- Exact native branch metadata determines the original BTYPE constructor. -/
theorem branch_encoding {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data) (mask : entry.data.mask = 16) :
    ∃ opcode imm rs1 rs2, entry.instruction = .BTYPE (imm,.Regidx rs2,.Regidx rs1,opcode) := by
  unfold decoderFields at fields
  split at fields
  all_goals first | (solve | cases fields) | (try (rw [← Option.some.inj fields] at mask; norm_num at mask))
  case h_5 =>
    rename_i _ imm rs2 rs1 opcode encoding
    exact ⟨opcode,imm,rs1,rs2,encoding⟩

/-- Public decoding selects the original branch clause; its native target,
    original reads and CSR preservation determine preparation/retirement. -/
theorem image_branch_retirement {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace) (decoded : Decoded trace setup)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    {w : Nat → ZMod mersenne31Modulus}
    (present : (⟨.jumpBranchSlt,w⟩ : Row mersenne31Modulus JumpBranchSltFamily) ∈ trace.rows)
    (mask : (w 12).val = 16)
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
  have entryMask : entry.data.mask = 16 := by
    rwa [packed,ZMod.val_natCast_of_lt small] at mask
  obtain ⟨opcode,imm,rs1,rs2,encoding⟩ := branch_encoding fields entryMask
  refine ⟨SailRV32.Functions.execute_BTYPE imm (.Regidx rs2) (.Regidx rs1) opcode,?_,?_⟩
  · rw [encoding]
    rfl
  · exact original_branch_step image inputs accepted decoded isa present fields query
      opcode imm rs1 rs2 encoding history past

/-- All original branch clauses retire in their constructed native segments. -/
theorem image_branch_execution {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup)
    (isa : ∃ value, before.regs.get? .misa = some value) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList)
      (rows : List (Row mersenne31Modulus JumpBranchSltFamily)) (after : State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) before after ∧
      SailStateMatches cells history after ∧
      ∀ newer row older, rows = newer ++ row :: older → (row.assignment 12).val = 16 →
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
      image_branch_retirement image inputs accepted decoded isa present mask source.fields query current earlier
    exact ⟨entry,member,rowBefore,rowAfter,clause,source,query,earlier,current,later,matched,retired⟩

end Airbender.JumpBranchSlt.Proofs
