import Airbender.Review.Circuits.ReducedMachine.Branch
import Airbender.Review.Helpers.Decoder.SparseSetup

namespace Airbender.ReducedMachine.Native
open Arithmetic

abbrev BranchMode := SailRV32.bop

def branchFunct3 (op : BranchMode) : Nat :=
  match op with
  | .BEQ => 0 | .BNE => 1 | .BLT => 4 | .BGE => 5 | .BLTU => 6 | .BGEU => 7

/-- Original BTYPE raw operands/offset and Sail sign extension. Native branch
    preprocessing fixes the dummy rd index to zero, retaining its actual port. -/
def branchDecoderFields : SailRV32.instruction → Option (Trace.DecoderData BranchMode)
  | .BTYPE (imm,.Regidx rs2,.Regidx rs1,op) =>
    some ⟨op,rs1,rs2,0,Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),
      branchMask,branchFunct3 op⟩
  | _ => none

abbrev BranchProgramEntry := Trace.ProgramEntry BranchMode
abbrev branchDecoderSetupImage := Trace.sparseDecoderSetupImageRunWith branchDecoderFields

structure BranchDecoded (w : Nat → ZMod mersenne31Modulus) (entry : BranchProgramEntry) : Prop where
  mask : w 12 = (branchMask : ZMod mersenne31Modulus)
  rs1 : w 5 = (entry.data.rs1.toNat : ZMod mersenne31Modulus)
  rs2 : w 6 = (entry.data.rs2.toNat : ZMod mersenne31Modulus)
  rd : rdIndex w = 0
  zero : rdZeroFlag w = 1
  immediate : #v[w 9,w 10] = #v[(entry.data.immediate.lo : ZMod mersenne31Modulus),
    (entry.data.immediate.hi : ZMod mersenne31Modulus)]
  funct3 : w 11 = (branchFunct3 entry.data.family : ZMod mersenne31Modulus)

end Airbender.ReducedMachine.Native
