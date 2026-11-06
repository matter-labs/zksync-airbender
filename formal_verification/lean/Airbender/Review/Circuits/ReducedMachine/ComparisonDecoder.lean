import Airbender.Review.Circuits.ReducedMachine.Comparison

namespace Airbender.ReducedMachine.Native
open Arithmetic

structure ComparisonMode where
  signed : Bool
  useRegister : Bool

def ComparisonMode.mask (mode : ComparisonMode) : Nat := comparisonMask mode.useRegister
def ComparisonMode.tag (mode : ComparisonMode) : Nat := if mode.signed then 2 else 3

def ComparisonMode.result (mode : ComparisonMode) (left right : BitVec 32) : BitVec 32 :=
  BitVec.ofNat 32 (if mode.signed then (if left.toInt < right.toInt then 1 else 0)
    else (if left.toNat < right.toNat then 1 else 0))

/-- Original SLT/SLTU/SLTI/SLTIU forms, with raw operands/x0 and Sail sign extension.
    This projection is separate from native Rust decoder-export/ROM enforcement. -/
def comparisonFields (signed useRegister : Bool) (rs1 rs2 rd : BitVec 5)
    (immediate : BitVec 32) : Option (Trace.DecoderData ComparisonMode) :=
  some ⟨⟨signed,useRegister⟩,rs1,rs2,rd,Word.ofBitVec immediate,
    comparisonMask useRegister,if signed then 2 else 3⟩

def comparisonDecoderFields : SailRV32.instruction → Option (Trace.DecoderData ComparisonMode)
  | .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.SLT) => comparisonFields true true rs1 rs2 rd 0
  | .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.SLTU) => comparisonFields false true rs1 rs2 rd 0
  | .ITYPE (imm,.Regidx rs1,.Regidx rd,.SLTI) =>
    comparisonFields true false rs1 0 rd (SailRV32.Functions.sign_extend (m := 32) imm)
  | .ITYPE (imm,.Regidx rs1,.Regidx rd,.SLTIU) =>
    comparisonFields false false rs1 0 rd (SailRV32.Functions.sign_extend (m := 32) imm)
  | _ => none

abbrev ComparisonProgramEntry := Trace.ProgramEntry ComparisonMode
abbrev comparisonDecoderSetupImage := Trace.sparseDecoderSetupImageRunWith comparisonDecoderFields

structure ComparisonDecoded (w : Nat → ZMod mersenne31Modulus) (entry : ComparisonProgramEntry) : Prop where
  mask : w 12 = (entry.data.family.mask : ZMod mersenne31Modulus)
  rs1 : w 5 = (entry.data.rs1.toNat : ZMod mersenne31Modulus)
  rs2 : w 6 = (entry.data.rs2.toNat : ZMod mersenne31Modulus)
  rd : rdIndex w = (entry.data.rd.toNat : ZMod mersenne31Modulus)
  zero : rdZeroFlag w = (if entry.data.rd = 0 then 1 else 0)
  immediate : #v[w 9,w 10] = #v[(entry.data.immediate.lo : ZMod mersenne31Modulus),
    (entry.data.immediate.hi : ZMod mersenne31Modulus)]
  funct3 : w 11 = (entry.data.family.tag : ZMod mersenne31Modulus)

end Airbender.ReducedMachine.Native
