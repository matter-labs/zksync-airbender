import Airbender.Review.Circuits.ReducedMachine.Bitwise

namespace Airbender.ReducedMachine.Native
open Arithmetic Verification

/-- Original bitwise operation and form, retaining immediate readonly rs2/x0. -/
structure BitwiseMode where
  kind : BinaryKind
  useRegister : Bool

def BitwiseMode.mask (mode : BitwiseMode) : Nat := bitwiseMask mode.useRegister

def BitwiseMode.result (mode : BitwiseMode) (left right : BitVec 32) : BitVec 32 :=
  byteOperation mode.kind.tag left right

/-- Original constructors and sign extension projected to actual native fields.
    This reference is separate from native decoder-export/ROM fidelity. -/
def bitwiseFields (kind : BinaryKind) (useRegister : Bool) (rs1 rs2 rd : BitVec 5)
    (immediate : BitVec 32) : Option (Trace.DecoderData BitwiseMode) :=
  some ⟨⟨kind,useRegister⟩,rs1,rs2,rd,Word.ofBitVec immediate,
    bitwiseMask useRegister,kind.tag⟩

def bitwiseDecoderFields : SailRV32.instruction → Option (Trace.DecoderData BitwiseMode)
  | .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.XOR) => bitwiseFields .xor true rs1 rs2 rd 0
  | .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.OR) => bitwiseFields .or true rs1 rs2 rd 0
  | .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.AND) => bitwiseFields .and true rs1 rs2 rd 0
  | .ITYPE (imm,.Regidx rs1,.Regidx rd,.XORI) =>
    bitwiseFields .xor false rs1 0 rd (SailRV32.Functions.sign_extend (m := 32) imm)
  | .ITYPE (imm,.Regidx rs1,.Regidx rd,.ORI) =>
    bitwiseFields .or false rs1 0 rd (SailRV32.Functions.sign_extend (m := 32) imm)
  | .ITYPE (imm,.Regidx rs1,.Regidx rd,.ANDI) =>
    bitwiseFields .and false rs1 0 rd (SailRV32.Functions.sign_extend (m := 32) imm)
  | _ => none

abbrev BitwiseProgramEntry := Trace.ProgramEntry BitwiseMode
abbrev bitwiseDecoderSetupImage := Trace.sparseDecoderSetupImageRunWith bitwiseDecoderFields

/-- Actual ten-field query observations recovered from an original instruction. -/
structure BitwiseDecoded (w : Nat → ZMod mersenne31Modulus) (entry : BitwiseProgramEntry) : Prop where
  mask : w 12 = (entry.data.family.mask : ZMod mersenne31Modulus)
  rs1 : w 5 = (entry.data.rs1.toNat : ZMod mersenne31Modulus)
  rs2 : w 6 = (entry.data.rs2.toNat : ZMod mersenne31Modulus)
  rd : rdIndex w = (entry.data.rd.toNat : ZMod mersenne31Modulus)
  zero : rdZeroFlag w = (if entry.data.rd = 0 then 1 else 0)
  immediate : #v[w 9,w 10] = #v[(entry.data.immediate.lo : ZMod mersenne31Modulus),
    (entry.data.immediate.hi : ZMod mersenne31Modulus)]
  funct3 : w 11 = (entry.data.family.kind.tag : ZMod mersenne31Modulus)

end Airbender.ReducedMachine.Native
