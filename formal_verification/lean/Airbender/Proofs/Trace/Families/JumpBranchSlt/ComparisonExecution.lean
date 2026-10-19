import Airbender.Proofs.Trace.Families.JumpBranchSlt.Comparisons
import Airbender.Proofs.Trace.Families.JumpBranchSlt.RegisterHistory
import Airbender.Proofs.Trace.Families.JumpBranchSlt.ComparisonPC
import Airbender.Proofs.Trace.Retirement

namespace Airbender.JumpBranchSlt.Comparison
open Arithmetic Trace Reference.RiscV.Sail

/-- The original source comparison constructors, including original x0 writes. -/
inductive Opcode where
  | slt | slti | sltu | sltiu
  deriving Repr, DecidableEq

def instruction (opcode : Opcode) (imm : BitVec 12) (rs1 rs2 rd : BitVec 5) : SailRV32.instruction :=
  match opcode with
  | .slt => .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.SLT)
  | .slti => .ITYPE (imm,.Regidx rs1,.Regidx rd,.SLTI)
  | .sltu => .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.SLTU)
  | .sltiu => .ITYPE (imm,.Regidx rs1,.Regidx rd,.SLTIU)

def data (opcode : Opcode) (imm : BitVec 12) (rs1 rs2 rd : BitVec 5) : DecoderData Unit :=
  match opcode with
  | .slt => ⟨(),rs1,rs2,rd,⟨0,0⟩,4,2⟩
  | .slti => ⟨(),rs1,0,rd,Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),8,2⟩
  | .sltu => ⟨(),rs1,rs2,rd,⟨0,0⟩,4,3⟩
  | .sltiu => ⟨(),rs1,0,rd,Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),8,3⟩

def clause (opcode : Opcode) (imm : BitVec 12) (rs1 rs2 rd : BitVec 5) : SailRV32.SailM SailRV32.ExecutionResult :=
  match opcode with
  | .slt => SailRV32.Functions.execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) .SLT
  | .slti => SailRV32.Functions.execute_ITYPE imm (.Regidx rs1) (.Regidx rd) .SLTI
  | .sltu => SailRV32.Functions.execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) .SLTU
  | .sltiu => SailRV32.Functions.execute_ITYPE imm (.Regidx rs1) (.Regidx rd) .SLTIU

end Airbender.JumpBranchSlt.Comparison

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification

/-- Reuse initialized native results and actual history accesses to execute
    each original Sail comparison clause. No desired result/read/state is supplied. -/
theorem image_comparison_clause {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace) (decoded : Decoded trace setup)
    {w : Nat → ZMod mersenne31Modulus}
    (present : (⟨.jumpBranchSlt,w⟩ : Row mersenne31Modulus JumpBranchSltFamily) ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (opcode : Comparison.Opcode) (imm : BitVec 12) (rs1 rs2 rd : BitVec 5)
    (encoding : entry.instruction = Comparison.instruction opcode imm rs1 rs2 rd)
    {before after : State}
    (history : SailHistory cells (rowEvents trace.memoryEpoch
      (⟨.jumpBranchSlt,w⟩ : Row mersenne31Modulus JumpBranchSltFamily)).reverse before after) :
    run (Comparison.clause opcode imm rs1 rs2 rd) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  have shape : entry.data = Comparison.data opcode imm rs1 rs2 rd := by
    rw [encoding] at fields
    cases opcode <;> simp only [Comparison.instruction,decoderFields] at fields
    all_goals exact (Option.some.inj fields).symm
  have packed := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) query
  change w 12 = (entry.data.mask : ZMod mersenne31Modulus) at packed
  have four : (4 : ZMod mersenne31Modulus).val = 4 := by decide
  have eight : (8 : ZMod mersenne31Modulus).val = 8 := by decide
  have maskValue : (w 12).val = entry.data.mask := by
    rw [packed,shape]
    cases opcode <;> first | exact four | exact eight
  have mask : (w 12).val ∈ [4,8] := by
    rw [maskValue,shape]
    cases opcode <;> simp [Comparison.data]
  have tag := query_tag (by decide) fields query
  have indices := Trace.Proofs.native_query_indices (by decide : limbBase < mersenne31Modulus) query
  have dest : (w 7).val = rd.toNat := by
    have eq := indices.2.2
    change (w 7).val = entry.data.rd.toNat at eq
    cases opcode <;> simpa only [shape,Comparison.data] using eq
  have offset := Trace.Proofs.native_query_immediate_word (by decide : limbBase < mersenne31Modulus)
    (decoder_field_bounds fields).1 query
  change (Word.mk (w 9).val (w 10).val) = entry.data.immediate at offset
  have reads := history_register_reads (by decide) trace.memoryEpoch history query
  have written := history_register_write (by decide) trace.memoryEpoch history query
  let left : Word := ⟨(w 22).val,(w 23).val⟩
  let right : Word := match opcode with
    | .slt | .sltu => ⟨(w 24).val,(w 25).val⟩
    | .slti | .sltiu => entry.data.immediate
  let output : Word := ⟨(w 38).val,(w 39).val⟩
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
    cases opcode
    case slt | sltu =>
      have bound := readBounds ⟨1,by decide⟩
      rw [Trace.Proofs.read_word] at bound
      exact bound
    case slti | sltiu => exact (decoder_field_bounds fields).1
  have actual := image_comparisons image inputs accepted decoded _ present mask
  dsimp only at actual
  have zero : rd.toNat = 0 ↔ rd = 0 := by
    constructor
    · intro eq; exact BitVec.eq_of_toNat_eq (by simpa using eq)
    · intro eq; simp [eq]
  have numerical : output.value = if rd = 0 then 0 else match opcode with
      | .slt | .slti => if left.toBitVec.toInt < right.toBitVec.toInt then 1 else 0
      | .sltu | .sltiu => if left.value < right.value then 1 else 0 := by
    rw [maskValue,tag,dest,shape] at actual
    cases opcode <;>
      simpa [Comparison.data,zero,left,right,output,← offset] using actual
  let result : BitVec 32 := match opcode with
    | .slt | .slti => SailRV32.Functions.zero_extend (m := 32)
      (SailRV32.Functions.bool_to_bit (SailRV32.Functions.zopz0zI_s left.toBitVec right.toBitVec))
    | .sltu | .sltiu => SailRV32.Functions.zero_extend (m := 32)
      (SailRV32.Functions.bool_to_bit (SailRV32.Functions.zopz0zI_u left.toBitVec right.toBitVec))
  have actualWrite : run (SailRV32.Functions.wX_bits (.Regidx rd) output.toBitVec) before = .ok () after := by
    cases opcode <;> simpa [shape,Comparison.data,memoryWord,MemoryPort.writeCode,
      WordColumns.code,WordColumns.evaluate,importedConstraintsMemoryPorts,output,Nat.unpair_pair] using written
  have resultWrite : run (SailRV32.Functions.wX_bits (.Regidx rd) result) before = .ok () after := by
    by_cases discarded : rd = 0
    · rw [discarded] at actualWrite ⊢
      change run (SailRV32.Functions.wX_bits zeroRegister _) before = _ at actualWrite ⊢
      rw [write_zero] at actualWrite ⊢
      exact actualWrite
    · have bitResult : output.toBitVec = result := by
        rw [if_neg discarded] at numerical
        cases opcode
        case slt | slti =>
          change BitVec.ofNat 32 output.value = _
          rw [numerical]
          by_cases lt : left.toBitVec.toInt < right.toBitVec.toInt <;>
            simp [result,lt,SailRV32.Functions.zero_extend,SailRV32.Functions.bool_to_bit,
              SailRV32.Functions.bool_bit_forwards,SailRV32.Functions.zopz0zI_s,_root_.Sail.BitVec.zeroExtend]
        case sltu | sltiu =>
          change BitVec.ofNat 32 output.value = _
          rw [numerical]
          by_cases lt : left.value < right.value <;>
            simp [result,lt,SailRV32.Functions.zero_extend,SailRV32.Functions.bool_to_bit,
              SailRV32.Functions.bool_bit_forwards,SailRV32.Functions.zopz0zI_u,_root_.Sail.BitVec.zeroExtend,
              _root_.Sail.BitVec.toNatInt,Word.toBitVec_toNat leftBound,Word.toBitVec_toNat rightBound]
      rw [← bitResult]
      exact actualWrite
  have leftRead : run (SailRV32.Functions.rX_bits (.Regidx rs1)) before = .ok left.toBitVec before := by
    cases opcode <;> simpa [shape,Comparison.data,memoryWord,MemoryPort.readCode,WordColumns.code,
      WordColumns.evaluate,importedConstraintsMemoryPorts,left,Nat.unpair_pair] using reads.1
  cases opcode
  case slt | sltu =>
    have rightRead : run (SailRV32.Functions.rX_bits (.Regidx rs2)) before = .ok right.toBitVec before := by
      simpa [shape,Comparison.data,memoryWord,MemoryPort.readCode,WordColumns.code,
        WordColumns.evaluate,importedConstraintsMemoryPorts,right,Nat.unpair_pair] using reads.2
    simp only [Comparison.clause,SailRV32.Functions.execute_RTYPE,freeM_bind_assoc,freeM_pure_bind]
    rw [run_bind_of_ok _ _ _ _ _ leftRead,run_bind_of_ok _ _ _ _ _ rightRead,
      run_bind_of_ok _ _ _ _ _ resultWrite]
    rfl
  case slti | sltiu =>
    have sign : right.toBitVec = SailRV32.Functions.sign_extend (m := 32) imm := by
      rw [show right = entry.data.immediate from rfl,shape]
      exact Word.ofBitVec_roundtrip _
    simp only [Comparison.clause,SailRV32.Functions.execute_ITYPE,freeM_bind_assoc,freeM_pure_bind]
    rw [run_bind_of_ok _ _ _ _ _ leftRead,← sign,run_bind_of_ok _ _ _ _ _ resultWrite]
    rfl

/-- Original decoder fields determine exactly the four comparison constructors. -/
theorem comparison_encoding {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data) (mask : entry.data.mask ∈ [4,8]) :
    ∃ opcode imm rs1 rs2 rd, entry.instruction = Comparison.instruction opcode imm rs1 rs2 rd := by
  unfold decoderFields at fields
  split at fields
  all_goals first | (solve | cases fields) | (try (rw [← Option.some.inj fields] at mask; norm_num at mask))
  case h_1 =>
    rename_i _ rs2 rs1 rd encoding
    exact ⟨.slt,0,rs1,rs2,rd,encoding⟩
  case h_2 =>
    rename_i _ rs2 rs1 rd encoding
    exact ⟨.sltu,0,rs1,rs2,rd,encoding⟩
  case h_3 =>
    rename_i _ imm rs1 rd encoding
    exact ⟨.slti,imm,rs1,0,rd,encoding⟩
  case h_4 =>
    rename_i _ imm rs1 rd encoding
    exact ⟨.sltiu,imm,rs1,0,rd,encoding⟩

/-- Shared original preparation/retirement lifts the native-derived clause.
    No prepared state, successor PC, operand value or result is supplied. -/
theorem image_comparison_retirement {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {initial : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ImageBoundary trace initial cells) (accepted : Accepted trace) (decoded : Decoded trace setup)
    {w : Nat → ZMod mersenne31Modulus}
    (present : (⟨.jumpBranchSlt,w⟩ : Row mersenne31Modulus JumpBranchSltFamily) ∈ trace.rows)
    (mask : (w 12).val ∈ [4,8])
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) {before after : State}
    (history : SailHistory cells (rowEvents trace.memoryEpoch
      (⟨.jumpBranchSlt,w⟩ : Row mersenne31Modulus JumpBranchSltFamily)).reverse before after) :
    ∃ clause, registerClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (Word.mk (w 13).val (w 14).val).toBitVec) := by
  have bounds := decoder_field_bounds fields
  have packed := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) query
  change w 12 = (entry.data.mask : ZMod mersenne31Modulus) at packed
  have small : entry.data.mask < mersenne31Modulus := by
    have choices := bounds.2.1
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at choices
    rcases choices with eq | eq | eq | eq | eq <;> rw [eq] <;> decide
  have entryMask : entry.data.mask ∈ [4,8] := by
    rwa [packed,ZMod.val_natCast_of_lt small] at mask
  obtain ⟨opcode,imm,rs1,rs2,rd,encoding⟩ := comparison_encoding fields entryMask
  refine ⟨Comparison.clause opcode imm rs1 rs2 rd,?_,?_⟩
  · rw [encoding]
    cases opcode <;> rfl
  · let pc := (Word.mk (w 0).val (w 1).val).toBitVec
    have prepared := Trace.Proofs.sail_history_control
      (Trace.Proofs.retired_state_history history pc) .nextPC (.inr rfl) (pc + 4)
    have clause := image_comparison_clause image inputs accepted decoded present fields query
      opcode imm rs1 rs2 rd encoding prepared
    have retired := normal_step_native _ (Trace.Proofs.retired_state_pc before pc) clause
    have target := (image_comparison_pc image accepted decoded _ present mask).1
    rw [target]
    change run (normalStep _) (retiredState before pc) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (pc + 4))
    change run (normalStep _) (retiredState before pc) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (retiredState after pc) (pc + 4)) at retired
    simpa only [Trace.Proofs.retired_state_overwrite] using retired

/-- Original comparison retirement in every constructed native history segment. -/
theorem image_comparison_execution {trace : Data mersenne31Modulus JumpBranchSltFamily}
    {setup : SparseDecoderSetup Unit} {before : State} {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ (history : TimestampSortedMemoryAccessList)
      (rows : List (Row mersenne31Modulus JumpBranchSltFamily)) (after : State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) before after ∧
      SailStateMatches cells history after ∧
      ∀ newer row older, rows = newer ++ row :: older → (row.assignment 12).val ∈ [4,8] →
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
      image_comparison_retirement image inputs accepted decoded present mask source.fields query current
    exact ⟨entry,member,rowBefore,rowAfter,clause,source,query,earlier,current,later,matched,retired⟩

end Airbender.JumpBranchSlt.Proofs
