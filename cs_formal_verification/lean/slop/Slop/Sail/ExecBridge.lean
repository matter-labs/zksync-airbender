import Slop.Sail.NextPCFrame
import Human.ISA.Sail.Airbender

/-! # Bridge: `Airbender.execute` on the Sail image of an AddSub instruction is `Reference.execution`

For each AddSub opcode, given that the row's operands are the instruction's fields (the caller's decode), the
Airbender execution of `toSail i` is the generated clause `Reference.execution` selects. -/

namespace Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem Configuration Airbender.Reference.Sail SailRV32 SailRV32.Functions Airbender

theorem execute_rtype_eq (next : BitVec 32) (rs2 rs1 rd : regidx) (op : rop) :
    Airbender.execute next (.RTYPE (rs2, rs1, rd, op)) = SailRV32.Functions.execute_RTYPE rs2 rs1 rd op := by
  unfold Airbender.execute SailRV32.Functions.execute
  dsimp only

theorem execute_itype_eq (next : BitVec 32) (imm : BitVec 12) (rs1 rd : regidx) (op : iop) :
    Airbender.execute next (.ITYPE (imm, rs1, rd, op)) = SailRV32.Functions.execute_ITYPE imm rs1 rd op := by
  unfold Airbender.execute SailRV32.Functions.execute
  dsimp only

theorem execute_utype_eq (next : BitVec 32) (imm : BitVec 20) (rd : regidx) (op : uop) :
    Airbender.execute next (.UTYPE (imm, rd, op)) = SailRV32.Functions.execute_UTYPE imm rd op := by
  unfold Airbender.execute SailRV32.Functions.execute
  dsimp only

/-- The generated clause of an input is its `registerClause` image. -/
theorem execution_eq_of (input : Input) (m : SailM ExecutionResult)
    (hm : registerClause (instruction input) = some m) : execution input = m := by
  unfold execution
  simp only [hm, Option.get_some]

theorem execute_toSail_add (next : BitVec 32) (input : Input) (rd rs1 rs2 : RV.Reg)
    (hop : input.row.opcode = .add) (h1 : input.rs1 = .Regidx rs1) (h2 : input.rs2 = .Regidx rs2)
    (hd : input.rd = .Regidx rd) :
    Airbender.execute next (toSail (.op .add rd rs1 rs2)) = execution input := by
  rw [execution_eq_of input (SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd .ADD)
    (by simp [instruction, registerClause, hop]), h1, h2, hd]
  rfl

theorem execute_toSail_sub (next : BitVec 32) (input : Input) (rd rs1 rs2 : RV.Reg)
    (hop : input.row.opcode = .sub) (h1 : input.rs1 = .Regidx rs1) (h2 : input.rs2 = .Regidx rs2)
    (hd : input.rd = .Regidx rd) :
    Airbender.execute next (toSail (.op .sub rd rs1 rs2)) = execution input := by
  rw [execution_eq_of input (SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd .SUB)
    (by simp [instruction, registerClause, hop]), h1, h2, hd]
  rfl

theorem execute_toSail_addi (next : BitVec 32) (input : Input) (imm : RV.Word) (rd rs1 : RV.Reg)
    (hop : input.row.opcode = .addi) (h1 : input.rs1 = .Regidx rs1) (himm : input.encodedImmediate = imm.extractLsb' 0 12)
    (hd : input.rd = .Regidx rd) :
    Airbender.execute next (toSail (.opImm .add rd rs1 imm)) = execution input := by
  rw [execution_eq_of input (SailRV32.Functions.execute_ITYPE input.encodedImmediate input.rs1 input.rd .ADDI)
    (by simp [instruction, registerClause, hop]), h1, himm, hd]
  rfl

theorem execute_toSail_lui (next : BitVec 32) (input : Input) (imm : RV.Word) (rd : RV.Reg)
    (hop : input.row.opcode = .lui) (himm : input.encodedUpperImmediate = imm.extractLsb' 12 20)
    (hd : input.rd = .Regidx rd) :
    Airbender.execute next (toSail (.lui rd imm)) = execution input := by
  rw [execution_eq_of input (SailRV32.Functions.execute_UTYPE input.encodedUpperImmediate input.rd .LUI)
    (by simp [instruction, registerClause, hop]), himm, hd]
  rfl

theorem execute_toSail_auipc (next : BitVec 32) (input : Input) (imm : RV.Word) (rd : RV.Reg)
    (hop : input.row.opcode = .auipc) (himm : input.encodedUpperImmediate = imm.extractLsb' 12 20)
    (hd : input.rd = .Regidx rd) :
    Airbender.execute next (toSail (.auipc rd imm)) = execution input := by
  rw [execution_eq_of input (SailRV32.Functions.execute_UTYPE input.encodedUpperImmediate input.rd .AUIPC)
    (by simp [instruction, registerClause, hop]), himm, hd]
  rfl

end Airbender.Reference.RiscV.Sail
