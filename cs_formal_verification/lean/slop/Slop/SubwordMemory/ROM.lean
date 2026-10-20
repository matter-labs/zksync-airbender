import Slop.SubwordMemory.Lookups

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

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem rom_values {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    {program : Nat → BitVec 32} {entry : Vector (ZMod p) 9} (byte : Bool)
    (h : (subwordTable program).Contains #[] entry)
    (selected : entry[8] = ((if byte then 45 else 44 : Nat) : ZMod p)) :
    ∃ i : Nat, i < (if byte then 8388608 else 4194304) ∧ entry[0] = (romKey byte i : ZMod p) ∧
      entry[1] = ((romData program byte i).1 : ZMod p) ∧ entry[2] = ((romData program byte i).2 : ZMod p) := by
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
  have natural : (subwordRow program i)[8] = (if byte then 45 else 44) := by
    apply bounded_nat_eq (F := ZMod p) (p := p) tagBound
      (by cases byte <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega)
    simpa only [Vector.getElem_map] using selected
  have indexBound := i.isLt
  cases byte <;> unfold subwordRow at natural ⊢ <;> dsimp only at natural ⊢
  all_goals split_ifs at natural ⊢
  all_goals solve
    | contradiction
    | (change (29 : Nat) = _ at natural; contradiction)
    | (change (30 : Nat) = _ at natural; contradiction)
    | (change (42 : Nat) = _ at natural; contradiction)
    | (change (43 : Nat) = _ at natural; contradiction)
    | (change (44 : Nat) = 45 at natural; contradiction)
    | (change (45 : Nat) = 44 at natural; contradiction)
    | (change (44 : Nat) = 44 at natural
       refine ⟨i.val - 655361, by omega, ?_, ?_, ?_⟩
       all_goals simp_all only [romKey, romData, Bool.false_eq_true, ite_false, Nat.div_one, Vector.getElem_map]
       all_goals rfl)
    | (change (45 : Nat) = 45 at natural
       refine ⟨i.val - 4849665, by omega, ?_, ?_, ?_⟩
       all_goals simp_all only [romKey, romData, ite_true, Vector.getElem_map]
       all_goals rfl)

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
    | (simp only [romKey, Bool.false_eq_true, ite_false, ite_true, Nat.div_one] at size key ⊢
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
    · simp only [word, half, native, Bool.false_eq_true, ite_false, Nat.div_one]
    · simp only [word, half, native, ite_true]
      apply (Nat.mod_eq_of_lt (show (program (cell.value / 4)).toNat / 65536 < 65536 by omega)).symm
  have slice := subword_extract byte highHalf highByte word wordBound aligned
  rw [nativeEq, halfEq] at slice
  cases byte
  · change _ = SailRV32.Functions.extend_value (!signed)
      ((program (cell.value / 4) >>> (8 * ((if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)))).setWidth 16)
    rw [slice]
    simp only [Bool.false_eq_true, ite_false]
  · change _ = SailRV32.Functions.extend_value (!signed)
      ((program (cell.value / 4) >>> (8 * ((if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)))).setWidth 8)
    rw [slice]
    simp only [ite_true]
end Airbender.Verification
