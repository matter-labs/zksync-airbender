import Airbender.Review.Circuits.ReducedMachine.BranchDecoder
import Airbender.Proofs.Arithmetic.Word
import Airbender.Proofs.Sail.ControlFlow

namespace Airbender.ReducedMachine.NativeBranchClauseProofs
open Native Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The pure comparison appearing inside the generated execute_BTYPE clause. -/
def nativeCondition (op : SailRV32.bop) (left right : BitVec 32) : Bool :=
  match op with
  | .BEQ => left == right | .BNE => left != right
  | .BLT => SailRV32.Functions.zopz0zI_s left right
  | .BGE => SailRV32.Functions.zopz0zKzJ_s left right
  | .BLTU => SailRV32.Functions.zopz0zI_u left right
  | .BGEU => SailRV32.Functions.zopz0zKzJ_u left right

/-- The six native predicates agree with the pure comparisons in original Sail. -/
theorem branch_condition_native (opcode : SailRV32.bop) (left right : Word)
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    branchCondition (branchFunct3 opcode) left right = nativeCondition opcode left.toBitVec right.toBitVec := by
  cases opcode <;> simp [branchCondition,branchFunct3,nativeCondition,
    SailRV32.Functions.zopz0zI_s,SailRV32.Functions.zopz0zKzJ_s,
    SailRV32.Functions.zopz0zI_u,SailRV32.Functions.zopz0zKzJ_u,_root_.Sail.BitVec.toNatInt,
    Word.toBitVec_toNat leftBound,Word.toBitVec_toNat rightBound]
  all_goals by_cases same : left.toBitVec = right.toBitVec <;> simp_all


/-- The original public projection admits only retained BTYPE instructions. -/
theorem encoding {entry : BranchProgramEntry}
    (fields : branchDecoderFields entry.instruction = some entry.data) :
    ∃ opcode imm rs1 rs2, entry.instruction = .BTYPE (imm,.Regidx rs2,.Regidx rs1,opcode) := by
  cases kind : entry.instruction
  case BTYPE args =>
    rcases args with ⟨imm,rs2,rs1,opcode⟩
    cases rs2 with
    | Regidx right =>
      cases rs1 with
      | Regidx left => exact ⟨opcode,imm,left,right,rfl⟩
  all_goals simp [branchDecoderFields,kind] at fields


/-- Pure retained BTYPE execution after normal nextPC preparation. The native
    client derives every read, predicate, target and alignment obligation. -/
theorem clause_of_reads (opcode : SailRV32.bop) (imm : BitVec 13)
    (rs1 rs2 : BitVec 5) (before : State) (left right pc final : BitVec 32)
    (leftRead : run (SailRV32.Functions.rX_bits (.Regidx rs1)) before = .ok left before)
    (rightRead : run (SailRV32.Functions.rX_bits (.Regidx rs2)) before = .ok right before)
    (architectural : run (SailRV32.readReg .PC) before = .ok pc before)
    (isa : ∃ value, before.regs.get? .misa = some value)
    (calculated : final = if nativeCondition opcode left right then
      pc+SailRV32.Functions.sign_extend (m := 32) imm else pc+4)
    (aligned : final.toNat % 4 = 0) :
    run (SailRV32.Functions.execute_BTYPE imm (.Regidx rs2) (.Regidx rs1) opcode)
      { before with regs := before.regs.insert .nextPC (pc+4) } =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        { before with regs := before.regs.insert .nextPC final } := by
  let taken := nativeCondition opcode left right
  let prepared : State := { before with regs := before.regs.insert .nextPC (pc+4) }
  let written : State := { before with regs := before.regs.insert .nextPC final }
  have leftPrepared := rX_nextPC (pc := pc+4) (.Regidx rs1) leftRead
  have rightPrepared := rX_nextPC (pc := pc+4) (.Regidx rs2) rightRead
  have pcPrepared := read_register_nextPC (pc+4) (by decide) architectural
  have reduced : run (SailRV32.Functions.execute_BTYPE imm (.Regidx rs2) (.Regidx rs1) opcode) prepared =
      run (if taken then SailRV32.Functions.jump_to (pc+SailRV32.Functions.sign_extend (m := 32) imm)
        else pure SailRV32.Functions.RETIRE_SUCCESS) prepared := by
    cases op : opcode <;> simp only [SailRV32.Functions.execute_BTYPE,freeM_bind_assoc,freeM_pure_bind]
    all_goals rw [run_bind_of_ok _ _ _ _ _ leftPrepared,run_bind_of_ok _ _ _ _ _ rightPrepared]
    all_goals simp only [taken,nativeCondition,op]
    all_goals split
    all_goals first | (rw [run_bind_of_ok _ _ _ _ _ pcPrepared]) | rfl
  change run _ prepared = .ok _ written
  rw [reduced]
  change final = if taken then _ else _ at calculated
  cases condition : taken
  · simp only [condition,Bool.false_eq_true,if_false] at calculated ⊢
    simp only [prepared,written,calculated]
    rfl
  · simp only [condition,if_true] at calculated ⊢
    obtain ⟨misa,read⟩ := isa
    have readable : run (SailRV32.readReg .misa) before = .ok misa before := read_register read
    have read' := read_register_nextPC (pc+4) (by decide) readable
    rw [← calculated]
    simpa only [prepared,written,nextPC_overwrite] using jump_to_aligned aligned read'

end Airbender.ReducedMachine.NativeBranchClauseProofs
