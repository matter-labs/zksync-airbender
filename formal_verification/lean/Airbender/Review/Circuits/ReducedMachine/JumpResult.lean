import Airbender.Review.Circuits.ReducedMachine.JumpDecoder
import Airbender.Review.Circuits.ReducedMachine.PC

namespace Airbender.ReducedMachine.Native
open Arithmetic

/-- Actual default return fields, distinct from the selected jump target. -/
def jumpLinkWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 49).val,(w 50).val⟩

/-- Numerical references only; original GPR/retained clause execution is separate. -/
def JumpMode.base (jal : JumpMode) (pc source : BitVec 32) : BitVec 32 := if jal then pc else source
def JumpMode.target (jal : JumpMode) (pc source immediate : BitVec 32) : BitVec 32 :=
  let raw := jal.base pc source + immediate
  if jal then raw else raw &&& 0xfffffffe

/-- Actual numerical words at original decoded fields. Sail GPR/clauses and
    physical public setup are separate; none of these results is an input. -/
def JumpNumericalEffects (w : Nat → ZMod mersenne31Modulus) (entry : JumpProgramEntry) : Prop :=
  candidateWord w = Word.ofBitVec ((initialPCWord w).toBitVec+4) ∧
  writtenWord w = (if entry.data.rd = 0 then ⟨0,0⟩ else Word.ofBitVec ((initialPCWord w).toBitVec+4)) ∧
  jumpRawTargetWord w = Word.ofBitVec
    (entry.data.family.base (initialPCWord w).toBitVec (sourceWord w).toBitVec+entry.data.immediate.toBitVec) ∧
  finalPCWord w = Word.ofBitVec
    (entry.data.family.target (initialPCWord w).toBitVec (sourceWord w).toBitVec entry.data.immediate.toBitVec) ∧
  (finalPCWord w).Bounded ∧ (finalPCWord w).toBitVec.toNat % 4 = 0

end Airbender.ReducedMachine.Native
