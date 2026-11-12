module
public import Slop.SubwordMemory.Lookups

@[expose] public section

namespace Airbender.Verification
open Airbender.Arithmetic

-- Decode only the modeled ROM row layout; Sail remains the instruction semantics.
attribute [local irreducible] Nat.sub
def romKey (byte : Bool) (i : Nat) : Nat :=
  4 * (i / (if byte then 8 else 4)) + 4194304 * (i / (if byte then 4 else 2) % 2) +
    8388608 * (i / (if byte then 2 else 1) % 2) + (if byte then 16777216 * (i % 2) else 0)

def romData (program : Nat → BitVec 32) (byte : Bool) (i : Nat) : Nat × Nat :=
  let half := (program (i / (if byte then 8 else 4))).toNat /
    (if i / (if byte then 2 else 1) % 2 = 1 then 65536 else 1) % 65536
  subwordLoadLimbs byte (half + 65536 * (i / (if byte then 4 else 2) % 2) +
    (if byte then 131072 * (i % 2) else 0))

theorem rom_values {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    {program : Nat → BitVec 32} {entry : Vector (ZMod p) 9} (byte : Bool)
    (h : (subwordTable program).Contains #[] entry)
    (selected : entry[8] = ((if byte then 45 else 44 : Nat) : ZMod p)) :
    ∃ i : Nat, i < (if byte then 8388608 else 4194304) ∧ entry[0] = (romKey byte i : ZMod p) ∧
      entry[1] = ((romData program byte i).1 : ZMod p) ∧ entry[2] = ((romData program byte i).2 : ZMod p) := by
  change ∃ i : Fin 13238273, entry = (subwordRow program i).map (fun (n : Nat) => (n : ZMod p)) at h
  obtain ⟨i, rfl⟩ := h
  have natural := subwordRow_tag (by omega)
    (by cases byte <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega) selected
  have indexBound := i.isLt
  cases byte <;> simp only [Bool.false_eq_true, ite_false, ite_true] at natural ⊢
  all_goals
    rcases subwordRow_regions program i with row | ⟨_, _, row⟩ | ⟨_, _, row⟩ | ⟨_, _, row⟩ | ⟨_, _, row⟩ |
      ⟨_, _, row⟩ | ⟨_, row⟩
  all_goals first
    | (rw [row] at natural; omega)
    | (rw [row, subwordDataRow_tag] at natural; omega)
    | (unfold subwordRow
       simp only [show ¬i.val = 0 by omega, show ¬i.val < 131073 by omega, show ¬i.val < 262145 by omega,
         show ¬i.val < 393217 by omega, show ¬i.val < 655361 by omega, show i.val < 4849665 by omega,
         ite_false, ite_true]
       refine ⟨i.val - 655361, by omega, ?_, ?_, ?_⟩
       all_goals simp only [romKey, romData, Bool.false_eq_true, ite_false, Nat.div_one, Vector.getElem_map,
         subwordDataRow_key, subwordDataRow_low, subwordDataRow_high, add_zero])
    | (unfold subwordRow
       simp only [show ¬i.val = 0 by omega, show ¬i.val < 131073 by omega, show ¬i.val < 262145 by omega,
         show ¬i.val < 393217 by omega, show ¬i.val < 655361 by omega, show ¬i.val < 4849665 by omega,
         ite_false]
       refine ⟨i.val - 4849665, by omega, ?_, ?_, ?_⟩
       all_goals simp only [romKey, romData, ite_true, Vector.getElem_map,
         subwordDataRow_key, subwordDataRow_low, subwordDataRow_high])

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
    exact (rv_subword_load_extension byte _).1
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

theorem rom_decode (byte signed highHalf highByte : Bool) {cell : Word} {i : Nat}
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

end Airbender.Verification
