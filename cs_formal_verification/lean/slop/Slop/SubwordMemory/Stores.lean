import Slop.SubwordMemory

namespace Airbender.SubwordMemory.Proofs
open Airbender.Arithmetic Airbender.Verification

/-- The unconditional clearing lookup preserves the old, unselected byte. -/
theorem clearing_data {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    {program : Nat → BitVec 32} {w : Nat → ZMod p} {old : Word}
    (highByte highHalf : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints (subwordTable program)))
    (bit0 : w 35 = if highByte then 1 else 0) (bit1 : w 36 = if highHalf then 1 else 0)
    (mapping : w 31 = (old.lo : ZMod p) ∧ w 32 = (old.hi : ZMod p)) (bounded : old.Bounded) :
    let half := if highHalf then old.hi else old.lo
    w 43 = ((if highByte then half % 256 else half - half % 256 : Nat) : ZMod p) := by
  let half := if highHalf then old.hi else old.lo
  let key := half + 65536 * (if highByte then 1 else 0)
  have halfBound : half < 65536 := by cases highHalf <;> first | exact bounded.1 | exact bounded.2
  have keyBound : key < 131072 := by cases highByte <;> simp [key] <;> omega
  have input : w 36 * w 32 + (1 - w 36) * w 31 + 65536 * w 35 = (key : ZMod p) := by
    cases highHalf <;> cases highByte <;> simp [key, half, mapping.1, mapping.2, bit0, bit1]
  have result := (subword_store_entry hp true key keyBound (clearing_query h)
    (by simp) input).1
  change w 43 = (subwordStoreContribution true key : ZMod p) at result
  rw [subword_store_packed true highByte half halfBound] at result
  exact result

/-- Byte stores take the source's low byte; halfword stores use the disabled
    table row, forcing zero contribution and preservation of the opposite half. -/
theorem store_contribution {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    {program : Nat → BitVec 32} {w : Nat → ZMod p} {source : Word}
    (byte highByte : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints (subwordTable program)))
    (active : w 4 = 1) (store : w 10 = 1) (ram : w 41 = 0)
    (selected : w 11 = if byte then 1 else 0) (bit0 : w 35 = if highByte then 1 else 0)
    (mapping : w 25 = (source.lo : ZMod p)) (bounded : source.Bounded) :
    w 36 * w 34 + (1 - w 36) * w 33 - w 11 * w 43 - (1 - w 11) * w 25 =
      ((if byte then (source.lo % 256) * (if highByte then 256 else 1) else 0 : Nat) : ZMod p) ∧
    w 36 * (w 33 - w 31) + (1 - w 36) * (w 34 - w 32) = 0 := by
  have query := store_query h active store ram
  cases byte
  · rw [selected] at query
    have result := subword_zero_values hp query (by simp)
    simpa [selected] using And.intro result.2.1 result.2.2
  · let key := source.lo + 65536 * (if highByte then 1 else 0)
    have keyBound : key < 131072 := by
      have low := bounded.1
      unfold limbBase at low
      cases highByte <;> simp [key] <;> omega
    rw [selected] at query
    have input : (1 : ZMod p) * (w 25 + 65536 * w 35) = (key : ZMod p) := by
      cases highByte <;> simp [key, bit0, mapping]
    have result := subword_store_entry hp false key keyBound query (by norm_num) input
    rw [subword_store_packed false highByte source.lo bounded.1] at result
    simpa [selected] using result

/-- The two store queries determine both new limbs and their bounds. In a byte
    store the selected half is cleared and filled; in a halfword store it is
    replaced by rs2's low half. The opposite half stays equal to the old cell. -/
theorem store_data {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    {program : Nat → BitVec 32} {w : Nat → ZMod p} {source old : Word}
    (byte highByte highHalf : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints (subwordTable program)))
    (active : w 4 = 1) (store : w 10 = 1) (ram : w 41 = 0)
    (selected : w 11 = if byte then 1 else 0)
    (bit0 : w 35 = if highByte then 1 else 0) (bit1 : w 36 = if highHalf then 1 else 0)
    (mapping : w 25 = (source.lo : ZMod p) ∧ w 31 = (old.lo : ZMod p) ∧ w 32 = (old.hi : ZMod p))
    (sourceBound : source.Bounded) (oldBound : old.Bounded) :
    let half := if highHalf then old.hi else old.lo
    let changed := if byte then
      (if highByte then half % 256 else half - half % 256) +
        (source.lo % 256) * (if highByte then 256 else 1)
      else source.lo
    let result := Word.mk (if highHalf then old.lo else changed) (if highHalf then changed else old.hi)
    result.Bounded ∧ Word.mk (w 33).val (w 34).val = result := by
  dsimp only
  let half := if highHalf then old.hi else old.lo
  let changed := if byte then
      (if highByte then half % 256 else half - half % 256) +
        (source.lo % 256) * (if highByte then 256 else 1)
      else source.lo
  have halfBound : half < 65536 := by cases highHalf <;> first | exact oldBound.1 | exact oldBound.2
  have changedBound : changed < 65536 := by
    have sourceLow := sourceBound.1
    have sourceByte : source.lo % 256 < 256 := Nat.mod_lt _ (by decide)
    have oldByte : half % 256 < 256 := Nat.mod_lt _ (by decide)
    unfold limbBase at sourceLow
    cases byte <;> cases highByte <;> simp [changed] <;> omega
  have cleared := clearing_data hp highByte highHalf h bit0 bit1 ⟨mapping.2.1, mapping.2.2⟩ oldBound
  have contributed := store_contribution hp byte highByte h active store ram selected bit0 mapping.1 sourceBound
  rw [cleared] at contributed
  have low : w 33 = ((if highHalf then old.lo else changed : Nat) : ZMod p) := by
    cases byte <;> cases highByte <;> cases highHalf <;>
      simp [changed, half, selected, bit1, mapping.1, mapping.2.1, mapping.2.2] at cleared contributed ⊢
    all_goals first | linear_combination contributed.2 | linear_combination contributed.1
  have high : w 34 = ((if highHalf then changed else old.hi : Nat) : ZMod p) := by
    cases byte <;> cases highByte <;> cases highHalf <;>
      simp [changed, half, selected, bit1, mapping.1, mapping.2.1, mapping.2.2] at cleared contributed ⊢
    all_goals first | linear_combination contributed.2 | linear_combination contributed.1
  have bounded : (Word.mk (if highHalf then old.lo else changed) (if highHalf then changed else old.hi)).Bounded := by
    cases highHalf <;> exact ⟨by first | exact changedBound | exact oldBound.1,
      by first | exact changedBound | exact oldBound.2⟩
  have lowSmall : (if highHalf then old.lo else changed) < p := by
    have small := bounded.1
    change (if highHalf then old.lo else changed) < limbBase at small
    unfold limbBase at small
    omega
  have highSmall : (if highHalf then changed else old.hi) < p := by
    have small := bounded.2
    change (if highHalf then changed else old.hi) < limbBase at small
    unfold limbBase at small
    omega
  refine ⟨bounded, ?_⟩
  rw [low, high, ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt lowSmall, Nat.mod_eq_of_lt highSmall]

set_option maxRecDepth 2048 in
/-- The proved merge changes exactly the selected byte window. -/
theorem store_byte_encoding {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    {program : Nat → BitVec 32} {w : Nat → ZMod p} {source old : Word}
    (byte highByte highHalf : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints (subwordTable program)))
    (active : w 4 = 1) (store : w 10 = 1) (ram : w 41 = 0)
    (selected : w 11 = if byte then 1 else 0)
    (bit0 : w 35 = if highByte then 1 else 0) (bit1 : w 36 = if highHalf then 1 else 0)
    (mapping : w 25 = (source.lo : ZMod p) ∧ w 31 = (old.lo : ZMod p) ∧ w 32 = (old.hi : ZMod p))
    (sourceBound : source.Bounded) (oldBound : old.Bounded)
    (aligned : byte = false → highByte = false) :
    let offset := (if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)
    ∀ i : Fin 4, (Word.mk (w 33).val (w 34).val).toBitVec.extractLsb' (8 * i.val) 8 =
      if offset ≤ i.val ∧ i.val < offset + (if byte then 1 else 2)
      then (source.toBitVec.setWidth (8 * (if byte then 1 else 2))).extractLsb' (8 * (i.val - offset)) 8
      else old.toBitVec.extractLsb' (8 * i.val) 8 := by
  have data := store_data hp byte highByte highHalf h active store ram selected bit0 bit1
    mapping sourceBound oldBound
  dsimp only
  rw [data.2]
  intro i
  have sourceNat := Word.toBitVec_toNat sourceBound
  have oldNat := Word.toBitVec_toNat oldBound
  have newNat := Word.toBitVec_toNat data.1
  have oldLow := oldBound.1
  have oldHigh := oldBound.2
  have sourceLow := sourceBound.1
  have sourceHigh := sourceBound.2
  unfold limbBase at oldLow oldHigh sourceLow sourceHigh
  cases byte <;> cases highByte <;> cases highHalf <;> fin_cases i
  all_goals solve
    | (have := aligned rfl; contradiction)
    | (simp only [Bool.false_eq_true, ite_false, ite_true] at newNat ⊢
       apply BitVec.eq_of_toNat_eq
       simp only [BitVec.extractLsb', BitVec.toNat_ofNat, BitVec.toNat_setWidth, sourceNat, oldNat, newNat]
       simp only [Bool.false_eq_true, ite_false, ite_true]
       norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.le_refl,
         Nat.zero_le, Nat.reduceLT, and_self, true_and, false_and, ite_false, ite_true,
         Nat.shiftRight_eq_div_pow, Nat.div_one]
       simp only [BitVec.toNat_ofNat, Word.value, limbBase]
       omega)

end Airbender.SubwordMemory.Proofs
