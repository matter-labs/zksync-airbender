import Airbender.Proofs.ShiftBinop.BinaryQueries
import Airbender.Proofs.Arithmetic.Bytes

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem append_value {n m : Nat} (x : BitVec n) (y : BitVec m) :
    (x.append y).toNat = x.toNat * 2 ^ m + y.toNat := by
  rw [BitVec.append_eq, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

def packBytes (a : Fin 4 → BitVec 8) : BitVec 32 :=
  BitVec.append (BitVec.append (a 3) (a 2)) (BitVec.append (a 1) (a 0))

/-- Byte bounds make the two native limbs a canonical RV32 concatenation. -/
theorem word_of_byte_pairs {word : Word} (a : Fin 4 → Nat)
    (small : ∀ i, a i < 256)
    (low : word.lo = a 0 + 256 * a 1) (high : word.hi = a 2 + 256 * a 3) :
    word.Bounded ∧ word.toBitVec = packBytes (fun i => BitVec.ofNat 8 (a i)) := by
  have b0 := small 0; have b1 := small 1; have b2 := small 2; have b3 := small 3
  have bounded : word.Bounded := by
    constructor <;> dsimp [limbBase] <;> omega
  refine ⟨bounded, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [Word.toBitVec_toNat bounded]
  simp only [packBytes,append_value,BitVec.toNat_ofNat,Nat.reducePow,
    Nat.mod_eq_of_lt (small _)]
  dsimp [Word.value,limbBase]
  rw [low,high]
  ring

/-- Ordinary byte operations commute with canonical RV32 concatenation. -/
theorem binary_pack (kind : BinaryKind) (a b : Fin 4 → BitVec 8) :
    byteOperation kind.tag (packBytes a) (packBytes b) =
      packBytes (fun i => byteOperation kind.tag (a i) (b i)) := by
  cases kind
  · simp only [byteOperation,BinaryKind.tag,packBytes,if_true]
    exact BitVec.xor_append.trans (congrArg₂ BitVec.append BitVec.xor_append BitVec.xor_append)
  · simp only [byteOperation,BinaryKind.tag,packBytes,Nat.reduceEqDiff,if_false,if_true]
    exact BitVec.or_append.trans (congrArg₂ BitVec.append BitVec.or_append BitVec.or_append)
  · simp only [byteOperation,BinaryKind.tag,packBytes,Nat.reduceEqDiff,if_false]
    exact BitVec.and_append.trans (congrArg₂ BitVec.append BitVec.and_append BitVec.and_append)

/-- Natural reconstruction follows only after native queries have bounded all bytes. -/
theorem binary_pair_values {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (kind : BinaryKind) (immediate : Bool)
    (mask : w 12 = ((8 + if immediate then 32 else 0 : Nat) : ZMod mersenne31Modulus))
    (tag : w 11 = (kind.tag : ZMod mersenne31Modulus)) :
    (w 23).val = (w 39).val + 256 * (w 43).val ∧
    (w 24).val = (w 47).val + 256 * (w 51).val ∧
    (w 27).val = (w 40).val + 256 * (w 44).val ∧
    (w 28).val = (w 48).val + 256 * (w 52).val ∧
    (w 55).val = (w 41).val + 256 * (w 45).val ∧
    (w 56).val = (w 49).val + 256 * (w 53).val := by
  obtain ⟨loA,hiA,loB,hiB,loC,hiC⟩ := binary_pairs holds immediate mask
  have b0 := binary_bytes holds kind immediate mask tag 0
  have b1 := binary_bytes holds kind immediate mask tag 1
  have b2 := binary_bytes holds kind immediate mask tag 2
  have b3 := binary_bytes holds kind immediate mask tag 3
  exact ⟨byte_pair_value (by decide) _ _ _ b0.1 b1.1 loA,
    byte_pair_value (by decide) _ _ _ b2.1 b3.1 hiA,
    byte_pair_value (by decide) _ _ _ b0.2.1 b1.2.1 loB,
    byte_pair_value (by decide) _ _ _ b2.2.1 b3.2.1 hiB,
    byte_pair_value (by decide) _ _ _ b0.2.2.1 b1.2.2.1 loC,
    byte_pair_value (by decide) _ _ _ b2.2.2.1 b3.2.2.1 hiC⟩

/-- Native byte queries force the exact selected RV32 word and all operand bounds. -/
theorem binary_selected {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (kind : BinaryKind) (immediate : Bool)
    (mask : w 12 = ((8 + if immediate then 32 else 0 : Nat) : ZMod mersenne31Modulus))
    (tag : w 11 = (kind.tag : ZMod mersenne31Modulus)) :
    (left w).Bounded ∧ (right w).Bounded ∧ (selectedWord w).Bounded ∧
    (selectedWord w).toBitVec = byteOperation kind.tag (left w).toBitVec (right w).toBitVec := by
  obtain ⟨loA,hiA,loB,hiB,loC,hiC⟩ := binary_pair_values holds kind immediate mask tag
  have bytes := binary_bytes holds kind immediate mask tag
  have a := word_of_byte_pairs (word := left w) (fun i => (w (39 + 4 * i.val)).val)
    (fun i => (bytes i).1) loA hiA
  have b := word_of_byte_pairs (word := right w) (fun i => (w (40 + 4 * i.val)).val)
    (fun i => (bytes i).2.1) loB hiB
  have c := word_of_byte_pairs (word := selectedWord w) (fun i => (w (41 + 4 * i.val)).val)
    (fun i => (bytes i).2.2.1) loC hiC
  refine ⟨a.1,b.1,c.1,?_⟩
  rw [a.2,b.2,binary_pack,c.2]
  congr 1
  funext i
  exact (bytes i).2.2.2

end Airbender.ShiftBinop.Proofs
