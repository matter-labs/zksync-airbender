import Airbender.Review.Helpers.Decoder.StatefulSetup

namespace Airbender.ShiftBinop
open Arithmetic

inductive Operation where
  | sll | srl | sra | xor | or | and
  deriving DecidableEq

/-- Native v2 operation bits; the immediate flag is a separate bit five. -/
def Operation.mask : Operation → Nat
  | .sll => 1 | .srl => 2 | .sra => 4 | _ => 8

def instructionFields (op : Operation) (immediate : Bool) (rs1 rs2 rd : BitVec 5)
    (word : Word) (funct3 : Nat) : Option (Trace.DecoderData Operation) :=
  some ⟨op,rs1,rs2,rd,word,op.mask + (if immediate then 32 else 0),funct3⟩

/-- Original ordinary RV32 forms projected to native v2 metadata. Preserve x0,
    full sign-extended 16-bit limbs and SRAI's encoded funct7 immediate bits.
    Custom CSR/oracle behavior and unsupported REV8/rotate forms are separate. -/
def decoderFields : SailRV32.instruction → Option (Trace.DecoderData Operation)
  | .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.SLL) => instructionFields .sll false rs1 rs2 rd ⟨0,0⟩ 1
  | .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.SRL) => instructionFields .srl false rs1 rs2 rd ⟨0,0⟩ 5
  | .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.SRA) => instructionFields .sra false rs1 rs2 rd ⟨0,0⟩ 5
  | .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.XOR) => instructionFields .xor false rs1 rs2 rd ⟨0,0⟩ 4
  | .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.OR) => instructionFields .or false rs1 rs2 rd ⟨0,0⟩ 6
  | .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.AND) => instructionFields .and false rs1 rs2 rd ⟨0,0⟩ 7
  | .ITYPE (imm,.Regidx rs1,.Regidx rd,.XORI) =>
    instructionFields .xor true rs1 0 rd (Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm)) 4
  | .ITYPE (imm,.Regidx rs1,.Regidx rd,.ORI) =>
    instructionFields .or true rs1 0 rd (Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm)) 6
  | .ITYPE (imm,.Regidx rs1,.Regidx rd,.ANDI) =>
    instructionFields .and true rs1 0 rd (Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm)) 7
  | .SHIFTIOP (amount,.Regidx rs1,.Regidx rd,.SLLI) =>
    if amount.toNat < 32 then instructionFields .sll true rs1 0 rd
      (Word.ofBitVec (BitVec.ofNat 32 (amount.toNat + 0))) 1 else none
  | .SHIFTIOP (amount,.Regidx rs1,.Regidx rd,.SRLI) =>
    if amount.toNat < 32 then instructionFields .srl true rs1 0 rd
      (Word.ofBitVec (BitVec.ofNat 32 (amount.toNat + 0))) 5 else none
  | .SHIFTIOP (amount,.Regidx rs1,.Regidx rd,.SRAI) =>
    if amount.toNat < 32 then instructionFields .sra true rs1 0 rd
      (Word.ofBitVec (BitVec.ofNat 32 (amount.toNat + 1024))) 5 else none
  | _ => none

abbrev ProgramEntry := Trace.ProgramEntry Operation
abbrev sparseDecoderSetupImage := Trace.sparseDecoderSetupImageRunWith decoderFields

end Airbender.ShiftBinop
