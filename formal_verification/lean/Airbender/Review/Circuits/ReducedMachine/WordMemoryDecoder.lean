import Airbender.Review.Circuits.ReducedMachine.WordMemory
import Airbender.Review.Circuits.ReducedMachine.Decoder

namespace Airbender.ReducedMachine.Native
open Arithmetic

abbrev WordMemoryMode := Bool

/-- Original LW/SW only. Keep raw operands, x0 and original Sail sign extension;
    this projection does not identify its public image with the fixed native ROM. -/
def wordMemoryFields (store : Bool) (rs1 rs2 rd : BitVec 5) (immediate : BitVec 32) :
    Option (Trace.DecoderData WordMemoryMode) :=
  some ⟨store,rs1,rs2,rd,Word.ofBitVec immediate,wordMemoryMask store,2⟩

def wordMemoryDecoderFields : SailRV32.instruction → Option (Trace.DecoderData WordMemoryMode)
  | .LOAD (imm,.Regidx rs1,.Regidx rd,false,4) =>
    wordMemoryFields false rs1 0 rd (SailRV32.Functions.sign_extend (m := 32) imm)
  | .STORE (imm,.Regidx rs2,.Regidx rs1,4) =>
    wordMemoryFields true rs1 rs2 0 (SailRV32.Functions.sign_extend (m := 32) imm)
  | _ => none

abbrev WordMemoryProgramEntry := Trace.ProgramEntry WordMemoryMode
abbrev wordMemoryDecoderSetupImage := Trace.sparseDecoderSetupImageRunWith wordMemoryDecoderFields

structure WordMemoryDecoded (w : Nat → ZMod mersenne31Modulus) (entry : WordMemoryProgramEntry) : Prop where
  mask : w 12 = (wordMemoryMask entry.data.family : ZMod mersenne31Modulus)
  rs1 : w 5 = (entry.data.rs1.toNat : ZMod mersenne31Modulus)
  rs2 : w 6 = (entry.data.rs2.toNat : ZMod mersenne31Modulus)
  rd : rdIndex w = (entry.data.rd.toNat : ZMod mersenne31Modulus)
  zero : rdZeroFlag w = (if entry.data.rd = 0 then 1 else 0)
  immediate : #v[w 9,w 10] = #v[(entry.data.immediate.lo : ZMod mersenne31Modulus),
    (entry.data.immediate.hi : ZMod mersenne31Modulus)]
  funct3 : w 11 = 2

end Airbender.ReducedMachine.Native
