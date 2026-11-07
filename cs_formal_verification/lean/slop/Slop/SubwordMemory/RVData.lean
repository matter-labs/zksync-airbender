import Slop.SubwordMemory
import Slop.SubwordMemory.ROM
import Slop.ISA.RV.MemSubword

/-! RV twins of the load-data lemmas (`Lookups.lean`, `ROM.lean`, `Data.lean`): the same table and constraint
    reasoning, with the result stated as `RV.exec`'s load extension (`RV.extendLoad`: `BitVec.signExtend` or
    `BitVec.setWidth`) instead of Sail's `extend_value`. The ROM case reuses `ROM.lean`'s private row decoders
    (`open private`), so that file and everything built on it stay unchanged. -/

namespace Airbender.Verification
open Airbender.Arithmetic

open private rom_values rom_decode romKey romData from Slop.SubwordMemory.ROM

/-- Twin of `subword_packed_extension`. -/
theorem rv_subword_packed_extension (byte signed highByte : Bool) (half : Nat) (bound : half < 65536) :
    let key := half + 65536 * (if signed then 1 else 0) + 131072 * (if highByte then 1 else 0)
    let data := subwordLoadLimbs byte key
    (Word.mk data.1 data.2).Bounded ∧ (Word.mk data.1 data.2).toBitVec =
      if byte then RV.extendLoad signed (BitVec.ofNat 8 (half / (if highByte then 256 else 1)))
      else RV.extendLoad signed (BitVec.ofNat 16 half) := by
  dsimp only
  let key := half + 65536 * (if signed then 1 else 0) + 131072 * (if highByte then 1 else 0)
  have low : key % 65536 = half := by cases signed <;> cases highByte <;> dsimp [key] <;> omega
  have sign : decide (key / 65536 % 2 = 1) = signed := by
    cases signed <;> cases highByte <;> simp [key] <;> omega
  have high : (key / 131072 % 2 = 1) ↔ highByte = true := by
    cases signed <;> cases highByte <;> simp [key] <;> omega
  have ext := rv_subword_load_extension byte key
  have canonical (n : Nat) : BitVec.ofNat 8 (n % 256) = BitVec.ofNat 8 n := by
    apply BitVec.eq_of_toNat_eq
    simp
  cases byte <;> simpa only [low, sign, high, Bool.false_eq_true, ite_false, ite_true, canonical] using ext

set_option maxRecDepth 4096 in
/-- Twin of `subword_rom_result`: ROM membership fixes the program word's slice and its RV extension. -/
theorem rv_subword_rom_result {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    {program : Nat → BitVec 32} {entry : Vector (ZMod p) 9} {cell : Word}
    (byte signed highByte highHalf : Bool)
    (h : (subwordTable program).Contains #[] entry)
    (selected : entry[8] = ((if byte then 45 else 44 : Nat) : ZMod p))
    (input : entry[0] = ((cell.value + 4194304 * (if signed then 1 else 0) +
      8388608 * (if highHalf then 1 else 0) + 16777216 * (if highByte then 1 else 0) : Nat) : ZMod p))
    (bounded : cell.Bounded) (inROM : cell.hi < 64) (aligned : byte = false → highByte = false) :
    let offset := (if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)
    let output := Word.mk entry[1].val entry[2].val
    output.Bounded ∧ output.toBitVec = RV.extendLoad signed
      ((program (cell.value / 4) >>> (8 * offset)).setWidth (8 * (if byte then 1 else 2))) := by
  obtain ⟨i, size, key, low, high⟩ := rom_values hp byte h selected
  have small : cell.value < 4194304 := by
    have lo := bounded.1
    unfold Word.value limbBase at *
    omega
  have inputBound : cell.value + 4194304 * (if signed then 1 else 0) +
      8388608 * (if highHalf then 1 else 0) + 16777216 * (if highByte then 1 else 0) < p := by
    cases signed <;> cases highHalf <;> cases highByte <;> simp <;> omega
  have keyBound : romKey byte i < p := by
    cases byte <;> simp only [romKey, Bool.false_eq_true, ite_false, ite_true, Nat.div_one] at size ⊢ <;> omega
  have natural := bounded_nat_eq (F := ZMod p) (p := p) inputBound keyBound (input.symm.trans key)
  have decoded := rom_decode byte signed highHalf highByte bounded inROM size aligned natural
  let half := (program (cell.value / 4)).toNat / (if highHalf then 65536 else 1) % 65536
  have halfBound : half < 65536 := Nat.mod_lt _ (by decide)
  have dataEq : romData program byte i =
      subwordLoadLimbs byte (half + 65536 * (if signed then 1 else 0) + 131072 * (if highByte then 1 else 0)) := by
    unfold romData
    rw [decoded.1, decoded.2.1, decoded.2.2.1]
    cases byte
    · have zero := aligned rfl
      rw [zero]
      simp [half]
    · rw [decoded.2.2.2 rfl]
      simp [half]
  rw [dataEq] at low high
  have extended := rv_subword_packed_extension byte signed highByte half halfBound
  have loSmall : (subwordLoadLimbs byte (half + 65536 * (if signed then 1 else 0) +
      131072 * (if highByte then 1 else 0))).1 < p := by
    have bound := extended.1.1
    change (subwordLoadLimbs byte (half + 65536 * (if signed then 1 else 0) +
      131072 * (if highByte then 1 else 0))).1 < limbBase at bound
    unfold limbBase at bound
    omega
  have hiSmall : (subwordLoadLimbs byte (half + 65536 * (if signed then 1 else 0) +
      131072 * (if highByte then 1 else 0))).2 < p := by
    have bound := extended.1.2
    change (subwordLoadLimbs byte (half + 65536 * (if signed then 1 else 0) +
      131072 * (if highByte then 1 else 0))).2 < limbBase at bound
    unfold limbBase at bound
    omega
  dsimp only
  rw [low, high, ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt loSmall, Nat.mod_eq_of_lt hiSmall]
  refine ⟨extended.1, ?_⟩
  rw [extended.2]
  let native := program (cell.value / 4)
  let word := Word.mk (native.toNat % 65536) (native.toNat / 65536)
  have nativeBound := native.isLt
  norm_num only [Nat.reducePow] at nativeBound
  have wordBound : word.Bounded := by
    constructor
    · exact Nat.mod_lt _ (by decide)
    · change native.toNat / 65536 < 65536
      omega
  have nativeEq : word.toBitVec = native := by
    apply BitVec.eq_of_toNat_eq
    simp only [word, Word.toBitVec, Word.value, limbBase, BitVec.toNat_ofNat]
    norm_num only [Nat.reducePow]
    omega
  have halfEq : (if highHalf then word.hi else word.lo) = half := by
    cases highHalf
    · simp only [word, half, native, Bool.false_eq_true, ite_false, Nat.div_one]
    · simp only [word, half, native, ite_true]
      apply (Nat.mod_eq_of_lt (show (program (cell.value / 4)).toNat / 65536 < 65536 by omega)).symm
  have slice := subword_extract byte highHalf highByte word wordBound aligned
  rw [nativeEq, halfEq] at slice
  cases byte
  · change _ = RV.extendLoad signed
      ((program (cell.value / 4) >>> (8 * ((if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)))).setWidth 16)
    rw [slice]
    simp only [Bool.false_eq_true, ite_false]
  · change _ = RV.extendLoad signed
      ((program (cell.value / 4) >>> (8 * ((if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)))).setWidth 8)
    rw [slice]
    simp only [ite_true]

end Airbender.Verification

namespace Airbender.SubwordMemory.Proofs
open Airbender.Arithmetic Airbender.Verification

/-- Twin of `ram_load_data`: a RAM load's result is the `RV.extendLoad` of the read word's slice. -/
theorem rv_ram_load_data {p : Nat} [Fact p.Prime] (hp : 262144 < p)
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
    output.Bounded ∧ output.toBitVec = RV.extendLoad signed
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
  have ext := rv_subword_packed_extension byte signed highByte half halfBound
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
  · change _ = RV.extendLoad signed
      ((readData.toBitVec >>> (8 * ((if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)))).setWidth 16)
    change _ = BitVec.ofNat 16 (if highHalf then readData.hi else readData.lo) at extracted
    rw [extracted]
    exact ext.2
  · change _ = RV.extendLoad signed
      ((readData.toBitVec >>> (8 * ((if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)))).setWidth 8)
    change _ = BitVec.ofNat 8 ((if highHalf then readData.hi else readData.lo) / (if highByte then 256 else 1)) at extracted
    rw [extracted]
    exact ext.2

/-- Twin of `rom_load_data`: a ROM load's result is the `RV.extendLoad` of the public program word's slice. -/
theorem rv_rom_load_data {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    {program : Nat → BitVec 32} {w : Nat → ZMod p} {cell : Word}
    (byte signed highByte highHalf : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints (subwordTable program)))
    (active : w 4 = 1) (load : w 10 = 0) (rom : w 41 = 1)
    (selected : w 11 = if byte then 1 else 0) (sign : w 12 = if signed then 1 else 0)
    (bit0 : w 35 = if highByte then 1 else 0) (bit1 : w 36 = if highHalf then 1 else 0)
    (mapping : cell.lo = (w 21).val ∧ w 22 = (cell.hi : ZMod p))
    (bounded : cell.Bounded) (inROM : cell.hi < 64) (aligned : byte = false → highByte = false) :
    let offset := (if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)
    let output := Word.mk (w 33).val (w 34).val
    output.Bounded ∧ output.toBitVec = RV.extendLoad signed
      ((program (cell.value / 4) >>> (8 * offset)).setWidth (8 * (if byte then 1 else 2))) := by
  have query := rom_load_query h active load rom
  have low : w 21 = (cell.lo : ZMod p) := by
    rw [mapping.1]
    exact (ZMod.natCast_zmod_val _).symm
  have packed : w 21 + 65536 * w 22 + 4194304 * w 12 + 8388608 * w 36 + 16777216 * w 35 =
      ((cell.value + 4194304 * (if signed then 1 else 0) + 8388608 * (if highHalf then 1 else 0) +
        16777216 * (if highByte then 1 else 0) : Nat) : ZMod p) := by
    cases signed <;> cases highHalf <;> cases highByte <;>
      simp [Word.value, limbBase, low, mapping.2, sign, bit0, bit1]
  rw [selected] at query
  exact rv_subword_rom_result hp byte signed highByte highHalf query
    (by cases byte <;> simp) packed bounded inROM aligned

end Airbender.SubwordMemory.Proofs
