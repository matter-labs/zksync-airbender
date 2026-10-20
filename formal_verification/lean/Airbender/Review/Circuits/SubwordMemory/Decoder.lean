import Airbender.Review.Helpers.Decoder.StatefulSetup
import Airbender.Review.Circuits.SubwordMemory.ValuesModel

namespace Airbender.SubwordMemory
open Arithmetic Trace
set_option autoImplicit false

inductive Operation where
  | lb | lh | lbu | lhu | sb | sh
  deriving DecidableEq

def Operation.mask : Operation → Nat
  | .sb | .sh => 1 | _ => 0

def Operation.funct3 : Operation → Nat
  | .lb | .sb => 0 | .lh | .sh => 1 | .lbu => 4 | .lhu => 5

/-- Original Sail subword forms projected to native v2 metadata. Preserve x0
    and signed immediates; clear exactly the unused native register index.
    Exported Rust decoder correspondence remains a separate fidelity boundary. -/
def decoderFields : SailRV32.instruction → Option (DecoderData Operation)
  | .LOAD (imm,.Regidx rs1,.Regidx rd,false,1) =>
    some ⟨.lb,rs1,0,rd,Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),0,0⟩
  | .LOAD (imm,.Regidx rs1,.Regidx rd,false,2) =>
    some ⟨.lh,rs1,0,rd,Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),0,1⟩
  | .LOAD (imm,.Regidx rs1,.Regidx rd,true,1) =>
    some ⟨.lbu,rs1,0,rd,Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),0,4⟩
  | .LOAD (imm,.Regidx rs1,.Regidx rd,true,2) =>
    some ⟨.lhu,rs1,0,rd,Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),0,5⟩
  | .STORE (imm,.Regidx rs2,.Regidx rs1,1) =>
    some ⟨.sb,rs1,rs2,0,Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),1,0⟩
  | .STORE (imm,.Regidx rs2,.Regidx rs1,2) =>
    some ⟨.sh,rs1,rs2,0,Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm),1,1⟩
  | _ => none

abbrev ProgramEntry := Trace.ProgramEntry Operation
abbrev sparseDecoderSetupImage := Trace.sparseDecoderSetupImageRunWith decoderFields
abbrev decoderQuery (w : Nat → ZMod mersenne31Modulus) :=
  nativeDecoderQuery importedConstraintsTraceColumns importedConstraintsDecoderColumns w

/-- Observed native fields fixed by the selected original public instruction. -/
structure DecodedFields (w : Nat → ZMod mersenne31Modulus) (entry : ProgramEntry) : Prop where
  store : w 12 = (entry.data.family.mask : Nat)
  funct3 : w 11 = (entry.data.family.funct3 : Nat)
  zero : w 8 = (if entry.data.rd = 0 then 1 else 0)
  indices : (w 5).val = entry.data.rs1.toNat ∧ (w 6).val = entry.data.rs2.toNat ∧
    (w 7).val = entry.data.rd.toNat
  pc : (⟨(w 0).val,(w 1).val⟩ : Word) = Word.ofBitVec entry.pc
  immediate : (⟨(w 9).val,(w 10).val⟩ : Word) = entry.data.immediate

/-- Actual decoded load writes; candidates already come from accepted helpers. -/
structure DecodedLoadWrites (w : Nat → ZMod mersenne31Modulus) (entry : ProgramEntry) : Prop where
  writes : #v[w 39,w 40] = (if entry.data.rd = 0 then #v[0,0] else #v[w 60,w 61])
  bounded : (⟨(w 39).val,(w 40).val⟩ : Word).Bounded

end Airbender.SubwordMemory
