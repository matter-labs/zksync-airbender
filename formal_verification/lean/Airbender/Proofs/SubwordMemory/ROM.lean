import Airbender.Proofs.Tables.SubwordCharacterization
import Airbender.Proofs.SubwordMemory.Lookups

namespace Airbender.Verification
open Airbender.Arithmetic

-- Decode only the modeled ROM row layout; Sail remains the instruction semantics.
attribute [local irreducible] Nat.sub
private def romKey (byte : Bool) (i : Nat) : Nat :=
  4 * (i / (if byte then 8 else 4)) + 4194304 * (i / (if byte then 4 else 2) % 2) +
    8388608 * (i / (if byte then 2 else 1) % 2) + (if byte then 16777216 * (i % 2) else 0)

private def romData (program : Nat → BitVec 32) (byte : Bool) (i : Nat) : Nat × Nat :=
  let half := (program (i / (if byte then 8 else 4))).toNat /
    (if i / (if byte then 2 else 1) % 2 = 1 then 65536 else 1) % 65536
  subwordLoadLimbs byte (half + 65536 * (i / (if byte then 4 else 2) % 2) +
    (if byte then 131072 * (i % 2) else 0))

private theorem tag_ite (condition : Prop) [Decidable condition]
    (a b : Vector Nat 9) :
    (if condition then a else b)[8] = if condition then a[8] else b[8] := by
  split <;> rfl

private theorem reference_rom_tag (program : Nat → BitVec 32) (i : Fin 13238273) :
    (referenceSubwordRow program i)[8] =
      if i.val = 0 then 0 else if i.val < 131073 then 29
      else if i.val < 262145 then 30 else if i.val < 393217 then 42
      else if i.val < 655361 then 43 else if i.val < 4849665 then 44 else 45 := by
  unfold referenceSubwordRow subwordRow
  simp only [tag_ite, subwordDataRow, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]

private theorem half_key (n : Nat) :
    romKey false n = 4 * (n / 4) + 4194304 * (n / 2 % 2) + 8388608 * (n % 2) := by
  simp only [romKey, Bool.false_eq_true, reduceIte, Nat.div_one, Nat.add_zero]

private theorem half_data (program : Nat → BitVec 32) (n : Nat) :
    romData program false n = subwordLoadLimbs false
      (((program (n / 4)).toNat / (if n % 2 = 1 then 65536 else 1)) % 65536 +
        65536 * (n / 2 % 2)) := by
  simp only [romData, Bool.false_eq_true, reduceIte, Nat.div_one, Nat.add_zero]

private theorem byte_key (n : Nat) :
    romKey true n = 4 * (n / 8) + 4194304 * (n / 4 % 2) +
      8388608 * (n / 2 % 2) + 16777216 * (n % 2) := by
  simp only [romKey, reduceIte]

private theorem byte_data (program : Nat → BitVec 32) (n : Nat) :
    romData program true n = subwordLoadLimbs true
      (((program (n / 8)).toNat / (if n / 2 % 2 = 1 then 65536 else 1)) % 65536 +
        65536 * (n / 4 % 2) + 131072 * (n % 2)) := by
  simp only [romData, reduceIte]

private theorem reference_half_row (program : Nat → BitVec 32) (i : Fin 13238273)
    (lower : 655361 ≤ i.val) (upper : i.val < 4849665) :
    referenceSubwordRow program i =
      subwordDataRow (romKey false (i.val - 655361))
        (romData program false (i.val - 655361)).1
        (romData program false (i.val - 655361)).2 44 := by
  unfold referenceSubwordRow subwordRow
  simp only [if_neg (show i.val ≠ 0 by omega),
    if_neg (show ¬i.val < 131073 by omega), if_neg (show ¬i.val < 262145 by omega),
    if_neg (show ¬i.val < 393217 by omega), if_neg (show ¬i.val < 655361 by omega),
    if_pos upper]
  rw [half_key, half_data]

private theorem reference_byte_row (program : Nat → BitVec 32) (i : Fin 13238273)
    (lower : 4849665 ≤ i.val) :
    referenceSubwordRow program i =
      subwordDataRow (romKey true (i.val - 4849665))
        (romData program true (i.val - 4849665)).1
        (romData program true (i.val - 4849665)).2 45 := by
  unfold referenceSubwordRow subwordRow
  simp only [if_neg (show i.val ≠ 0 by omega),
    if_neg (show ¬i.val < 131073 by omega), if_neg (show ¬i.val < 262145 by omega),
    if_neg (show ¬i.val < 393217 by omega), if_neg (show ¬i.val < 655361 by omega),
    if_neg (show ¬i.val < 4849665 by omega)]
  rw [byte_key, byte_data]

private theorem mapped_field {p : Nat} {entry : Vector (ZMod p) 9} {row : Vector Nat 9}
    (equal : entry = row.map (fun n : Nat => (n : ZMod p))) (lane : Fin 9) :
    entry[lane.val] = (row[lane.val] : ZMod p) := by
  simpa only [Vector.getElem_map] using
    congrArg (fun values : Vector (ZMod p) 9 => values[lane.val]) equal

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem rom_values_reference {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    {program : Nat → BitVec 32} {entry : Vector (ZMod p) 9} (byte : Bool)
    (h : ∃ i : Fin 13238273, entry =
      (referenceSubwordRow program i).map (fun n : Nat => (n : ZMod p)))
    (selected : entry[8] = ((if byte then 45 else 44 : Nat) : ZMod p)) :
    ∃ i : Nat, i < (if byte then 8388608 else 4194304) ∧ entry[0] = (romKey byte i : ZMod p) ∧
      entry[1] = ((romData program byte i).1 : ZMod p) ∧ entry[2] = ((romData program byte i).2 : ZMod p) := by
  obtain ⟨i, equal⟩ := h
  have tagBound : (referenceSubwordRow program i)[8] < p := by
    rw [reference_rom_tag]
    split_ifs <;> omega
  have natural : (referenceSubwordRow program i)[8] = (if byte then 45 else 44) := by
    apply bounded_nat_eq (F := ZMod p) (p := p) tagBound
      (by cases byte <;> simp only [Bool.false_eq_true, reduceIte] <;> omega)
    exact (mapped_field equal ⟨8, by decide⟩).symm.trans selected
  rw [reference_rom_tag] at natural
  have indexBound := i.isLt
  have region : if byte then 4849665 ≤ i.val else 655361 ≤ i.val ∧ i.val < 4849665 := by
    cases byte <;> simp only [Bool.false_eq_true, reduceIte] at natural ⊢
    all_goals split_ifs at natural <;> omega
  cases byte
  · simp only [Bool.false_eq_true, reduceIte] at region ⊢
    have shape := equal.trans (congrArg (fun row : Vector Nat 9 =>
      row.map (fun n : Nat => (n : ZMod p))) (reference_half_row program i region.1 region.2))
    refine ⟨i.val - 655361, by omega, ?_, ?_, ?_⟩
    · exact mapped_field shape ⟨0, by decide⟩
    · exact mapped_field shape ⟨1, by decide⟩
    · exact mapped_field shape ⟨2, by decide⟩
  · simp only [reduceIte] at region ⊢
    have shape := equal.trans (congrArg (fun row : Vector Nat 9 =>
      row.map (fun n : Nat => (n : ZMod p))) (reference_byte_row program i region))
    refine ⟨i.val - 4849665, by omega, ?_, ?_, ?_⟩
    · exact mapped_field shape ⟨0, by decide⟩
    · exact mapped_field shape ⟨1, by decide⟩
    · exact mapped_field shape ⟨2, by decide⟩

set_option maxRecDepth 4096 in
private theorem rom_values {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    {program : Nat → BitVec 32} {entry : Vector (ZMod p) 9} (byte : Bool)
    (h : (subwordTable program).Contains #[] entry)
    (selected : entry[8] = ((if byte then 45 else 44 : Nat) : ZMod p)) :
    ∃ i : Nat, i < (if byte then 8388608 else 4194304) ∧ entry[0] = (romKey byte i : ZMod p) ∧
      entry[1] = ((romData program byte i).1 : ZMod p) ∧ entry[2] = ((romData program byte i).2 : ZMod p) := by
  apply rom_values_reference hp byte ?_ selected
  change ∃ i : Fin 13238273, entry =
    (subwordNativeRow program i).map (fun n : Nat => (n : ZMod p)) at h
  obtain ⟨i, equal⟩ := h
  exact ⟨i, equal.trans (congrArg (fun row : Vector Nat 9 =>
    row.map (fun n : Nat => (n : ZMod p))) (subwordNativeRow_eq_reference program i))⟩

/-- Every modeled ROM row returns canonical result limbs, independently of
    address/key reconstruction. This supplies native history's write bounds. -/
theorem subword_rom_bounds {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    {program : Nat → BitVec 32} {entry : Vector (ZMod p) 9} (byte : Bool)
    (h : (subwordTable program).Contains #[] entry)
    (selected : entry[8] = ((if byte then 45 else 44 : Nat) : ZMod p)) :
    (Word.mk entry[1].val entry[2].val).Bounded := by
  obtain ⟨i, _, _, low, high⟩ := rom_values hp byte h selected
  have canonical : (Word.mk (romData program byte i).1 (romData program byte i).2).Bounded := by
    dsimp only [romData]
    exact (subword_load_extension byte _).1
  have loSmall : (romData program byte i).1 < p := by
    have bound := canonical.1
    dsimp [limbBase] at bound
    omega
  have hiSmall : (romData program byte i).2 < p := by
    have bound := canonical.2
    dsimp [limbBase] at bound
    omega
  rw [low, high, ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt loSmall, Nat.mod_eq_of_lt hiSmall]
  exact canonical

private theorem rom_decode (byte signed highHalf highByte : Bool) {cell : Word} {i : Nat}
    (bounded : cell.Bounded) (inROM : cell.hi < 64)
    (size : i < (if byte then 8388608 else 4194304))
    (aligned : byte = false → highByte = false)
    (key : cell.value + 4194304 * (if signed then 1 else 0) +
      8388608 * (if highHalf then 1 else 0) + 16777216 * (if highByte then 1 else 0) = romKey byte i) :
    i / (if byte then 8 else 4) = cell.value / 4 ∧
    i / (if byte then 4 else 2) % 2 = (if signed then 1 else 0) ∧
    i / (if byte then 2 else 1) % 2 = (if highHalf then 1 else 0) ∧
    (byte = true → i % 2 = (if highByte then 1 else 0)) := by
  have low := bounded.1
  have small : cell.value < 4194304 := by unfold Word.value limbBase at *; omega
  have halves : i / 2 / 2 = i / 4 := by omega
  have quarters : i / 4 / 2 = i / 8 := by omega
  simp only [Word.value, limbBase] at small key ⊢
  cases byte <;> cases signed <;> cases highHalf <;> cases highByte
  all_goals solve
    | (have := aligned rfl; contradiction)
    | (simp only [romKey, Bool.false_eq_true, if_false, if_true, Nat.div_one] at size key ⊢
       have signBit : i / 4 % 2 < 2 := Nat.mod_lt _ (by decide)
       have halfBit : i / 2 % 2 < 2 := Nat.mod_lt _ (by decide)
       have byteBit : i % 2 < 2 := Nat.mod_lt _ (by decide)
       interval_cases i / 4 % 2 <;> interval_cases i / 2 % 2 <;> interval_cases i % 2 <;>
         simp only [limbBase] at * <;> first
         | omega
         | (have baseEq : cell.lo + 65536 * cell.hi = 4 * (i / 4) := by omega
            rw [baseEq]
            simp)
         | (have baseEq : cell.lo + 65536 * cell.hi = 4 * (i / 8) := by omega
            rw [baseEq]
            simp))

set_option maxRecDepth 4096 in
/-- ROM membership fixes the actual program slice and Sail's extension. The
    key bound accounts for the four packed address/sign/position fields. -/
theorem subword_rom_result {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    {program : Nat → BitVec 32} {entry : Vector (ZMod p) 9} {cell : Word}
    (byte signed highByte highHalf : Bool)
    (h : (subwordTable program).Contains #[] entry)
    (selected : entry[8] = ((if byte then 45 else 44 : Nat) : ZMod p))
    (input : entry[0] = ((cell.value + 4194304 * (if signed then 1 else 0) +
      8388608 * (if highHalf then 1 else 0) + 16777216 * (if highByte then 1 else 0) : Nat) : ZMod p))
    (bounded : cell.Bounded) (inROM : cell.hi < 64) (aligned : byte = false → highByte = false) :
    let offset := (if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)
    let output := Word.mk entry[1].val entry[2].val
    output.Bounded ∧ output.toBitVec = SailRV32.Functions.extend_value (!signed)
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
    cases byte <;> simp only [romKey, Bool.false_eq_true, if_false, if_true, Nat.div_one] at size ⊢ <;> omega
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
  have extended := subword_packed_extension byte signed highByte half halfBound
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
    · simp only [word, half, native, Bool.false_eq_true, if_false, Nat.div_one]
    · simp only [word, half, native, if_true]
      apply (Nat.mod_eq_of_lt (show (program (cell.value / 4)).toNat / 65536 < 65536 by omega)).symm
  have slice := subword_extract byte highHalf highByte word wordBound aligned
  rw [nativeEq, halfEq] at slice
  cases byte
  · change _ = SailRV32.Functions.extend_value (!signed)
      ((program (cell.value / 4) >>> (8 * ((if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)))).setWidth 16)
    rw [slice]
    simp only [Bool.false_eq_true, if_false]
  · change _ = SailRV32.Functions.extend_value (!signed)
      ((program (cell.value / 4) >>> (8 * ((if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)))).setWidth 8)
    rw [slice]
    simp only [if_true]
end Airbender.Verification
