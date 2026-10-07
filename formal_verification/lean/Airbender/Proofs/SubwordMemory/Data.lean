import Airbender.Proofs.SubwordMemory

namespace Airbender.SubwordMemory.Proofs
open Airbender.Arithmetic Airbender.Verification

/-- Eliminate the packed RAM key using bounded input limbs and the imported
    selectors. The resulting operation is Sail's own extension of a word slice. -/
theorem ram_load_data {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    {program : Nat → BitVec 32} {w : Nat → ZMod p} {readData : Word}
    (byte signed highByte highHalf : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints (subwordTable program)))
    (active : w 4 = 1) (load : w 10 = 0) (ram : w 41 = 0)
    (selected : w 11 = if byte then 1 else 0) (sign : w 12 = if signed then 1 else 0)
    (bit0 : w 35 = if highByte then 1 else 0) (bit1 : w 36 = if highHalf then 1 else 0)
    (mapping : w 25 = (readData.lo : ZMod p) ∧ w 26 = (readData.hi : ZMod p))
    (bounded : readData.Bounded) (aligned : byte = false → highByte = false) :
    let offset := (if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)
    let output := Word.mk (w 33).val (w 34).val
    output.Bounded ∧ output.toBitVec = SailRV32.Functions.extend_value (!signed)
      ((readData.toBitVec >>> (8 * offset)).setWidth (8 * (if byte then 1 else 2))) := by
  dsimp only
  let half := if highHalf then readData.hi else readData.lo
  let key := half + 65536 * (if signed then 1 else 0) + 131072 * (if highByte then 1 else 0)
  have halfBound : half < 65536 := by
    cases highHalf <;> first | exact bounded.1 | exact bounded.2
  have keyBound : key < p := by
    cases signed <;> cases highByte <;> simp [key] <;> omega
  have query := ram_load_query h active load ram
  have keyEq : w 36 * w 26 + (1 - w 36) * w 25 + 65536 * w 12 + 131072 * w 35 =
      (key : ZMod p) := by
    cases highHalf <;> cases highByte <;> cases signed <;>
      simp [key, half, bit0, bit1, sign, mapping.1, mapping.2]
  rw [keyEq, selected] at query
  obtain ⟨actual, actualBound, actualEq, low, high⟩ :=
    subword_ram_values hp byte query (by cases byte <;> simp)
  have actualSmall : actual < p := by cases byte <;> simp at actualBound <;> omega
  have equal : key = actual := bounded_nat_eq (F := ZMod p) (p := p) keyBound actualSmall actualEq
  subst actual
  have ext := subword_packed_extension byte signed highByte half halfBound
  have lowSmall : (subwordLoadLimbs byte key).1 < p := by
    have small := ext.1.1
    change (subwordLoadLimbs byte key).1 < limbBase at small
    unfold limbBase at small
    omega
  have highSmall : (subwordLoadLimbs byte key).2 < p := by
    have small := ext.1.2
    change (subwordLoadLimbs byte key).2 < limbBase at small
    unfold limbBase at small
    omega
  change w 33 = ((subwordLoadLimbs byte key).1 : ZMod p) at low
  change w 34 = ((subwordLoadLimbs byte key).2 : ZMod p) at high
  rw [low, high, ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt lowSmall, Nat.mod_eq_of_lt highSmall]
  refine ⟨ext.1, ?_⟩
  have extracted := subword_extract byte highHalf highByte readData bounded aligned
  cases byte
  · change _ = SailRV32.Functions.extend_value (!signed)
      ((readData.toBitVec >>> (8 * ((if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)))).setWidth 16)
    change _ = BitVec.ofNat 16 (if highHalf then readData.hi else readData.lo) at extracted
    rw [extracted]
    exact ext.2
  · change _ = SailRV32.Functions.extend_value (!signed)
      ((readData.toBitVec >>> (8 * ((if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)))).setWidth 8)
    change _ = BitVec.ofNat 8 ((if highHalf then readData.hi else readData.lo) / (if highByte then 256 else 1)) at extracted
    rw [extracted]
    exact ext.2

end Airbender.SubwordMemory.Proofs
