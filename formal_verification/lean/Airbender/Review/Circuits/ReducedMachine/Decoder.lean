import Airbender.Review.Circuits.ReducedMachine.Row
import Airbender.Review.Circuits.ReducedMachine.ShiftWrite
import Airbender.Review.Helpers.Decoder.StatefulSetup

namespace Airbender.ReducedMachine.Native
open Arithmetic

/-- Native reduced funct3 values for the selected original RV32 shift forms. -/
def ShiftMode.funct3 : ShiftMode → Nat
  | .left => 1 | _ => 5

def shiftFields (mode : ShiftMode) (useRegister : Bool) (rs1 rs2 rd : BitVec 5)
    (word : Word) : Option (Trace.DecoderData ShiftMode) :=
  some ⟨mode,rs1,rs2,rd,word,mode.mask useRegister,mode.funct3⟩

/-- Selected original RV32 shifts projected to actual reduced decoder metadata.
    Preserve x0 opcodes/operands and encoded SRAI funct7 bits; public byte decoding
    is performed by the shared original Sail construction. Other combined families
    remain unsupported by this selected projection. -/
def shiftDecoderFields : SailRV32.instruction → Option (Trace.DecoderData ShiftMode)
  | .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.SLL) => shiftFields .left true rs1 rs2 rd ⟨0,0⟩
  | .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.SRL) => shiftFields .right true rs1 rs2 rd ⟨0,0⟩
  | .RTYPE (.Regidx rs2,.Regidx rs1,.Regidx rd,.SRA) => shiftFields .arithmetic true rs1 rs2 rd ⟨0,0⟩
  | .SHIFTIOP (amount,.Regidx rs1,.Regidx rd,.SLLI) =>
    if amount.toNat < 32 then shiftFields .left false rs1 0 rd
      (Word.ofBitVec (BitVec.ofNat 32 amount.toNat)) else none
  | .SHIFTIOP (amount,.Regidx rs1,.Regidx rd,.SRLI) =>
    if amount.toNat < 32 then shiftFields .right false rs1 0 rd
      (Word.ofBitVec (BitVec.ofNat 32 amount.toNat)) else none
  | .SHIFTIOP (amount,.Regidx rs1,.Regidx rd,.SRAI) =>
    if amount.toNat < 32 then shiftFields .arithmetic false rs1 0 rd
      (Word.ofBitVec (BitVec.ofNat 32 (amount.toNat + 1024))) else none
  | _ => none

abbrev ShiftProgramEntry := Trace.ProgramEntry ShiftMode
abbrev shiftDecoderSetupImage := Trace.sparseDecoderSetupImageRunWith shiftDecoderFields

def decoderQuery {p : Nat} (w : Nat → ZMod p) : Vector (ZMod p) 10 :=
  Trace.nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

/-- Actual decoder fields interpreted at one recovered original public instruction.
    These are conclusions of membership, not extra per-row hypotheses. -/
structure ShiftDecoded (w : Nat → ZMod mersenne31Modulus) (entry : ShiftProgramEntry) : Prop where
  mask : ∃ useRegister : Bool, w 12 = (entry.data.family.mask useRegister : ZMod mersenne31Modulus)
  rs1 : w 5 = (entry.data.rs1.toNat : ZMod mersenne31Modulus)
  rs2 : w 6 = (entry.data.rs2.toNat : ZMod mersenne31Modulus)
  rd : rdIndex w = (entry.data.rd.toNat : ZMod mersenne31Modulus)
  zero : rdZeroFlag w = (if entry.data.rd = 0 then 1 else 0)
  immediate : #v[w 9,w 10] = #v[(entry.data.immediate.lo : ZMod mersenne31Modulus),
    (entry.data.immediate.hi : ZMod mersenne31Modulus)]
  funct3 : w 11 = (entry.data.family.funct3 : ZMod mersenne31Modulus)

end Airbender.ReducedMachine.Native
