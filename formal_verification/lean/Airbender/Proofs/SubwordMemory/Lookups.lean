import Airbender.Review.SubwordTables
import Airbender.Proofs.Arithmetic.Word
import Airbender.Proofs.Sail.Memory

namespace Airbender.Verification
open Airbender.Arithmetic

-- Keep symbolic offsets opaque during reduction; omega handles their arithmetic.
attribute [local irreducible] Nat.sub

private theorem subwordDataRow_key (key lo hi tag : Nat) :
    (subwordDataRow key lo hi tag)[0] = key := rfl
private theorem subwordDataRow_low (key lo hi tag : Nat) :
    (subwordDataRow key lo hi tag)[1] = lo := rfl
private theorem subwordDataRow_high (key lo hi tag : Nat) :
    (subwordDataRow key lo hi tag)[2] = hi := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Read the fixed RAM-load regions of the native Clean setup table. Other
    regions, including caller-selected ROM words, cannot satisfy these tags. -/
theorem subword_ram_values {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    {program : Nat → BitVec 32} {entry : Vector (ZMod p) 9} (byte : Bool)
    (h : (subwordTable program).Contains #[] entry)
    (selected : entry[8] = ((if byte then 43 else 42 : Nat) : ZMod p)) :
    ∃ key : Nat, key < (if byte then 262144 else 131072) ∧ entry[0] = (key : ZMod p) ∧
      entry[1] = ((subwordLoadLimbs byte key).1 : ZMod p) ∧
      entry[2] = ((subwordLoadLimbs byte key).2 : ZMod p) := by
  change ∃ i : Fin 13238273, entry = (subwordRow program i).map (fun (n : Nat) => (n : ZMod p)) at h
  obtain ⟨i, rfl⟩ := h
  have tagBound : (subwordRow program i)[8] < p := by
    unfold subwordRow
    dsimp only
    split_ifs <;> first
      | (change (0 : Nat) < p; omega)
      | (change (29 : Nat) < p; omega)
      | (change (30 : Nat) < p; omega)
      | (change (42 : Nat) < p; omega)
      | (change (43 : Nat) < p; omega)
      | (change (44 : Nat) < p; omega)
      | (change (45 : Nat) < p; omega)
  have natural : (subwordRow program i)[8] = (if byte then 43 else 42) := by
    apply bounded_nat_eq (F := ZMod p) (p := p) tagBound
      (by cases byte <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega)
    simpa only [Vector.getElem_map] using selected
  have indexBound := i.isLt
  cases byte <;> unfold subwordRow at natural ⊢ <;> dsimp only at natural ⊢
  all_goals split_ifs at natural ⊢
  all_goals solve
    | contradiction
    | (change (29 : Nat) = _ at natural; contradiction)
    | (change (30 : Nat) = _ at natural; contradiction)
    | (change (44 : Nat) = _ at natural; contradiction)
    | (change (45 : Nat) = _ at natural; contradiction)
    | (change (42 : Nat) = 43 at natural; contradiction)
    | (change (43 : Nat) = 42 at natural; contradiction)
    | (change (42 : Nat) = 42 at natural
       refine ⟨i.val - 262145, ?_, ?_, ?_, ?_⟩ <;> first
         | omega
         | (rw [Vector.getElem_map, subwordDataRow_key])
         | (rw [Vector.getElem_map, subwordDataRow_low])
         | (rw [Vector.getElem_map, subwordDataRow_high]))
    | (change (43 : Nat) = 43 at natural
       refine ⟨i.val - 393217, ?_, ?_, ?_, ?_⟩ <;> first
         | omega
         | (rw [Vector.getElem_map, subwordDataRow_key])
         | (rw [Vector.getElem_map, subwordDataRow_low])
         | (rw [Vector.getElem_map, subwordDataRow_high]))

-- Encoding lemma: the reference operation here is Sail's own extend_value.
theorem extend_subword_limbs (byte signed : Bool) (value : Nat)
    (bound : value < (if byte then 256 else 65536)) :
    let negative := signed = true ∧ (if byte then 128 else 32768) ≤ value
    let result := Word.mk (value + if byte && negative then 65280 else 0)
      (if negative then 65535 else 0)
    result.Bounded ∧ result.toBitVec =
      if byte then SailRV32.Functions.extend_value (!signed) (BitVec.ofNat 8 value)
      else SailRV32.Functions.extend_value (!signed) (BitVec.ofNat 16 value) := by
  dsimp only
  cases byte <;> cases signed
  all_goals
    simp at bound ⊢
    constructor
    · simp [Word.Bounded, limbBase]
      first | omega | (split_ifs <;> omega)
    · apply BitVec.eq_of_toNat_eq
      simp only [Word.toBitVec, Word.value, limbBase, SailRV32.Functions.extend_value,
        SailRV32.Functions.zero_extend, SailRV32.Functions.sign_extend, Sail.BitVec.zeroExtend,
        Sail.BitVec.signExtend, Bool.false_eq_true, if_false, if_true,
        BitVec.zeroExtend, BitVec.toNat_signExtend, BitVec.msb_eq_decide,
        BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      norm_num only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Bool.false_and,
        Bool.true_and, Bool.and_true, Bool.and_false, Bool.decide_coe]
      have canonical : value % 65536 = value := Nat.mod_eq_of_lt (by omega)
      try rw [canonical]
      first | omega | (split_ifs <;> norm_num at * <;> omega)

/-- Decode the table's sign-extension packing using the actual Sail function. -/
theorem subword_load_extension (byte : Bool) (key : Nat) :
    let value := if byte then (key % 65536) / (if key / 131072 % 2 = 1 then 256 else 1) % 256
      else key % 65536
    let data := subwordLoadLimbs byte key
    (Word.mk data.1 data.2).Bounded ∧ (Word.mk data.1 data.2).toBitVec =
      if byte then SailRV32.Functions.extend_value (!(decide (key / 65536 % 2 = 1))) (BitVec.ofNat 8 value)
      else SailRV32.Functions.extend_value (!(decide (key / 65536 % 2 = 1))) (BitVec.ofNat 16 value) := by
  let value := if byte then (key % 65536) / (if key / 131072 % 2 = 1 then 256 else 1) % 256
    else key % 65536
  have bound : value < (if byte then 256 else 65536) := by
    cases byte <;> dsimp [value] <;> exact Nat.mod_lt _ (by decide)
  have result := extend_subword_limbs byte (decide (key / 65536 % 2 = 1)) value bound
  simpa [subwordLoadLimbs, value] using result

/-- RAM-load membership forces bounded output limbs and Sail's byte/halfword
    extension. The key is read canonically from the imported lookup. -/
theorem subword_ram_extension {p : Nat} [Fact p.Prime] (hp : 262144 < p)
    {program : Nat → BitVec 32} {entry : Vector (ZMod p) 9} (byte : Bool)
    (h : (subwordTable program).Contains #[] entry)
    (selected : entry[8] = ((if byte then 43 else 42 : Nat) : ZMod p)) :
    let key := entry[0].val
    let value := if byte then (key % 65536) / (if key / 131072 % 2 = 1 then 256 else 1) % 256
      else key % 65536
    let output := Word.mk entry[1].val entry[2].val
    output.Bounded ∧ output.toBitVec =
      if byte then SailRV32.Functions.extend_value (!(decide (key / 65536 % 2 = 1))) (BitVec.ofNat 8 value)
      else SailRV32.Functions.extend_value (!(decide (key / 65536 % 2 = 1))) (BitVec.ofNat 16 value) := by
  obtain ⟨key, keyBound, keyEq, lo, hi⟩ := subword_ram_values hp byte h selected
  have bound : key < p := by cases byte <;> simp at keyBound <;> omega
  have keyVal : entry[0].val = key := by rw [keyEq, ZMod.val_natCast, Nat.mod_eq_of_lt bound]
  have extended := subword_load_extension byte key
  have lowBound : (subwordLoadLimbs byte key).1 < p := by
    have low := extended.1.1
    change (subwordLoadLimbs byte key).1 < limbBase at low
    unfold limbBase at low
    omega
  have highBound : (subwordLoadLimbs byte key).2 < p := by
    have high := extended.1.2
    change (subwordLoadLimbs byte key).2 < limbBase at high
    unfold limbBase at high
    omega
  simp only [lo, hi, keyVal, ZMod.val_natCast, Nat.mod_eq_of_lt lowBound, Nat.mod_eq_of_lt highBound]
  exact extended

theorem subword_packed_extension (byte signed highByte : Bool) (half : Nat) (bound : half < 65536) :
    let key := half + 65536 * (if signed then 1 else 0) + 131072 * (if highByte then 1 else 0)
    let data := subwordLoadLimbs byte key
    (Word.mk data.1 data.2).Bounded ∧ (Word.mk data.1 data.2).toBitVec =
      if byte then SailRV32.Functions.extend_value (!signed)
        (BitVec.ofNat 8 (half / (if highByte then 256 else 1)))
      else SailRV32.Functions.extend_value (!signed) (BitVec.ofNat 16 half) := by
  dsimp only
  let key := half + 65536 * (if signed then 1 else 0) + 131072 * (if highByte then 1 else 0)
  have low : key % 65536 = half := by cases signed <;> cases highByte <;> dsimp [key] <;> omega
  have sign : decide (key / 65536 % 2 = 1) = signed := by
    cases signed <;> cases highByte <;> simp [key] <;> omega
  have high : (key / 131072 % 2 = 1) ↔ highByte = true := by
    cases signed <;> cases highByte <;> simp [key] <;> omega
  have ext := subword_load_extension byte key
  have canonical (n : Nat) : BitVec.ofNat 8 (n % 256) = BitVec.ofNat 8 n := by
    apply BitVec.eq_of_toNat_eq
    simp
  cases byte <;> simpa only [low, sign, high, Bool.false_eq_true, if_false, if_true, canonical] using ext

theorem subword_extract (byte highHalf highByte : Bool) (word : Word) (bound : word.Bounded)
    (aligned : byte = false → highByte = false) :
    let offset := (if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)
    let half := if highHalf then word.hi else word.lo
    if byte then
      (word.toBitVec >>> (8 * offset)).setWidth 8 = BitVec.ofNat 8 (half / (if highByte then 256 else 1))
    else (word.toBitVec >>> (8 * offset)).setWidth 16 = BitVec.ofNat 16 half := by
  have canonical := Word.toBitVec_toNat bound
  have lo := bound.1
  have hi := bound.2
  unfold limbBase at lo hi
  cases byte <;> cases highHalf <;> cases highByte
  all_goals first
    | (have := aligned rfl; contradiction)
    | (simp only [Bool.false_eq_true, if_false, if_true]
       apply BitVec.eq_of_toNat_eq
       simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, canonical]
       norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.div_one, Nat.shiftRight_eq_div_pow]
       unfold Word.value limbBase
       omega)

end Airbender.Verification
