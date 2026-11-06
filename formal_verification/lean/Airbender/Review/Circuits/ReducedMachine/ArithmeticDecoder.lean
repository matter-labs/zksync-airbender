import Airbender.Review.Circuits.ReducedMachine.ArithmeticResult

namespace Airbender.ReducedMachine.Native
open Arithmetic

/-- Original arithmetic constructors projected to the actual reduced metadata.
    Keep original x0 instructions/operands, sign extension and raw U-type funct3.
    This is a reference projection, not a Rust decoder-export certificate. -/
def arithmeticFields (mode : ArithmeticMode) (rs1 rs2 rd : BitVec 5)
    (immediate : BitVec 32) (funct3 : Nat := 0) : Option (Trace.DecoderData ArithmeticMode) :=
  some ⟨mode,rs1,rs2,rd,Word.ofBitVec immediate,mode.mask,funct3⟩

def arithmeticDecoderFields : SailRV32.instruction → Option (Trace.DecoderData ArithmeticMode)
  | .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.ADD) => arithmeticFields .add rs1 rs2 rd 0
  | .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.SUB) => arithmeticFields .sub rs1 rs2 rd 0
  | .ITYPE (imm,.Regidx rs1,.Regidx rd,.ADDI) =>
    arithmeticFields .addi rs1 0 rd (SailRV32.Functions.sign_extend (m := 32) imm)
  | .UTYPE (imm,.Regidx rd,.LUI) =>
    arithmeticFields .lui 0 0 rd (imm ++ BitVec.ofNat 12 0) (imm.toNat % 8)
  | .UTYPE (imm,.Regidx rd,.AUIPC) =>
    arithmeticFields .auipc 0 0 rd (imm ++ BitVec.ofNat 12 0) (imm.toNat % 8)
  | _ => none

abbrev ArithmeticProgramEntry := Trace.ProgramEntry ArithmeticMode
abbrev arithmeticDecoderSetupImage := Trace.sparseDecoderSetupImageRunWith arithmeticDecoderFields

/-- Actual fields recovered from one original public arithmetic instruction. -/
structure ArithmeticDecoded (w : Nat → ZMod mersenne31Modulus) (entry : ArithmeticProgramEntry) : Prop where
  mask : w 12 = (entry.data.family.mask : ZMod mersenne31Modulus)
  rs1 : w 5 = (entry.data.rs1.toNat : ZMod mersenne31Modulus)
  rs2 : w 6 = (entry.data.rs2.toNat : ZMod mersenne31Modulus)
  rd : rdIndex w = (entry.data.rd.toNat : ZMod mersenne31Modulus)
  zero : rdZeroFlag w = (if entry.data.rd = 0 then 1 else 0)
  immediate : #v[w 9,w 10] = #v[(entry.data.immediate.lo : ZMod mersenne31Modulus),
    (entry.data.immediate.hi : ZMod mersenne31Modulus)]
  funct3 : w 11 = (entry.data.funct3 : ZMod mersenne31Modulus)

end Airbender.ReducedMachine.Native
