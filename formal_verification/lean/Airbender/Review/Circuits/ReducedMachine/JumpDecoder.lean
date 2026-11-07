import Airbender.Review.Circuits.ReducedMachine.Jump
import Airbender.Review.Helpers.Decoder.SparseSetup

namespace Airbender.ReducedMachine.Native
open Arithmetic

/-- True is original JAL; false is original JALR. -/
abbrev JumpMode := Bool

/-- Retain original x0/raw operands, Sail sign extension and raw JAL funct3. -/
def jumpDecoderFields : SailRV32.instruction → Option (Trace.DecoderData JumpMode)
  | .JAL (imm,.Regidx rd) => some ⟨true,0,0,rd,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),jumpMask true,imm.toNat / 4096 % 8⟩
  | .JALR (imm,.Regidx rs1,.Regidx rd) => some ⟨false,rs1,0,rd,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),jumpMask false,0⟩
  | _ => none

abbrev JumpProgramEntry := Trace.ProgramEntry JumpMode
abbrev jumpDecoderSetupImage := Trace.sparseDecoderSetupImageRunWith jumpDecoderFields

structure JumpDecoded (w : Nat → ZMod mersenne31Modulus) (entry : JumpProgramEntry) : Prop where
  mask : w 12 = (jumpMask entry.data.family : ZMod mersenne31Modulus)
  rs1 : w 5 = (entry.data.rs1.toNat : ZMod mersenne31Modulus)
  rs2 : w 6 = (entry.data.rs2.toNat : ZMod mersenne31Modulus)
  rd : rdIndex w = (entry.data.rd.toNat : ZMod mersenne31Modulus)
  zero : rdZeroFlag w = (if entry.data.rd = 0 then 1 else 0)
  immediate : #v[w 9,w 10] = #v[(entry.data.immediate.lo : ZMod mersenne31Modulus),
    (entry.data.immediate.hi : ZMod mersenne31Modulus)]
  funct3 : w 11 = (entry.data.funct3 : ZMod mersenne31Modulus)

end Airbender.ReducedMachine.Native
