module
public import Human.Helpers.Decoder.RVProgram
public import Human.Circuits.ShiftBinop.Decoder

@[expose] public section

namespace Airbender.ShiftBinop
open Arithmetic

/-- Native metadata from `binary_shifts_family/decoder.rs`, on `RV.Instr` (as `decoderFields`). Discarded
    destinations belong to ADD/SUB; shift amounts of 32 or more (never decoded) fail. -/
def rvDecoderFields : RV.Instr → Option (Trace.DecoderData Unit)
  | .op .xor rd rs1 rs2 => instructionFields .xor rs1 rs2 rd ⟨0, 0⟩
  | .op .or rd rs1 rs2 => instructionFields .or rs1 rs2 rd ⟨0, 0⟩
  | .op .and rd rs1 rs2 => instructionFields .and rs1 rs2 rd ⟨0, 0⟩
  | .op .sll rd rs1 rs2 => instructionFields .sll rs1 rs2 rd ⟨0, 0⟩
  | .op .srl rd rs1 rs2 => instructionFields .srl rs1 rs2 rd ⟨0, 0⟩
  | .op .sra rd rs1 rs2 => instructionFields .sra rs1 rs2 rd ⟨0, 0⟩
  | .opImm .xor rd rs1 imm => instructionFields .xor rs1 0 rd (binaryImmediate imm)
  | .opImm .or rd rs1 imm => instructionFields .or rs1 0 rd (binaryImmediate imm)
  | .opImm .and rd rs1 imm => instructionFields .and rs1 0 rd (binaryImmediate imm)
  | .opImm .sll rd rs1 imm => if imm.toNat < 32 then instructionFields .sll rs1 0 rd ⟨imm.toNat, 0⟩ else none
  | .opImm .srl rd rs1 imm => if imm.toNat < 32 then instructionFields .srl rs1 0 rd ⟨imm.toNat, 0⟩ else none
  | .opImm .sra rd rs1 imm => if imm.toNat < 32 then instructionFields .sra rs1 0 rd ⟨imm.toNat, 0⟩ else none
  | .rev8 rd rs1 => instructionFields .rev8 rs1 0 rd ⟨0, 0⟩
  | _ => none

abbrev RVProgramEntry := Trace.RVProgramEntry Unit
abbrev rvDecoderTable {p : Nat} [Fact p.Prime] (program : List RVProgramEntry) :=
  Trace.rvDecoderTable (p := p) program ()

end Airbender.ShiftBinop
