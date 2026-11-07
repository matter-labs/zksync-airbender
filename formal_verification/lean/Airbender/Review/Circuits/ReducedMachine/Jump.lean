import Airbender.Review.Circuits.ReducedMachine.Comparison

namespace Airbender.ReducedMachine.Native
open Arithmetic Verification

/-- Actual update-rd/JUMP_COMMON_KEY bits, plus the original JAL minor flag. -/
def jumpMask (jal : Bool) : Nat := if jal then 33025 else 257

def jumpCandidate (w : Nat → ZMod mersenne31Modulus) : Vector (ZMod mersenne31Modulus) 2 := #v[w 116,w 117]
def jumpBaseWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 81).val,(w 82).val⟩
def jumpImmediateWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 9).val,(w 10).val⟩
def jumpRawTargetWord (w : Nat → ZMod mersenne31Modulus) : Word := ⟨(w 61).val,(w 62).val⟩

/-- Actual local fields. Original public decoding, numerical input addition and
    original Sail execution are separate obligations; all three ports remain. -/
def JumpRouting (w : Nat → ZMod mersenne31Modulus) (jal : Bool) : Prop :=
  source2 w = #v[w 9,w 10] ∧ (w 39 = w 6 ∧ w 40 = 0 ∧ w 88 = 1) ∧
  #v[w 81,w 82] = (if jal then #v[w 0,w 1] else #v[w 35,w 36]) ∧
  w 81+w 9 = w 61+65536*w 95 ∧ w 95+w 82+w 10 = w 62+65536*w 63 ∧
  #v[w 100,w 101,w 102,w 103] = #v[w 61,w 64,w 65,17] ∧ w 64 = 0 ∧
  jumpCandidate w = defaultPC w ∧
  rdPort.address.code w = Nat.pair 0 (Nat.pair (rdIndex w).val 0) ∧
  rdWrite w = (jumpCandidate w).map (fun value => (1-rdZeroFlag w)*value) ∧
  finalPC w = #v[w 65,w 62]

end Airbender.ReducedMachine.Native
