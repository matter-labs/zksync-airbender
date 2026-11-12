module
public import Slop.ShiftBinop.Lookups
public import Human.ISA.RV32
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Airbender.Verification
open Airbender.Arithmetic

-- Algebraic helpers for combining lookup outputs; the REV8 branch is our spec's `RV.rev8`.
def shiftOperation (tag : Nat) (x : BitVec 32) (amount : Nat) : BitVec 32 :=
  if tag = 1 then x.shiftLeft amount else if tag = 2 then x.ushiftRight amount
  else if tag = 3 then x.sshiftRight amount else RV.rev8 x

set_option maxRecDepth 16384 in
theorem rev8_bytes (x : BitVec 32) : RV.rev8 x =
    ((x.extractLsb' 0 8) ++ (x.extractLsb' 8 8)) ++ ((x.extractLsb' 16 8) ++ (x.extractLsb' 24 8)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [RV.rev8, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases k <;> simp

/-- Numerical form used to assemble the circuit's four byte contributions. -/
theorem rev8_value (x : BitVec 32) :
    (RV.rev8 x).toNat =
      16777216 * (x.extractLsb' 0 8).toNat + 65536 * (x.extractLsb' 8 8).toNat +
      256 * (x.extractLsb' 16 8).toNat + (x.extractLsb' 24 8).toNat := by
  have append_value {m n : Nat} (a : BitVec m) (b : BitVec n) :
      (a ++ b).toNat = a.toNat * 2 ^ n + b.toNat := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
  rw [rev8_bytes, append_value, append_value, append_value]
  norm_num
  ring

private theorem contribution_eq (tag : Nat) (valid : tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 5)
    (x : BitVec 32) (amount : Nat) (reverse : tag = 5 → amount = 0) (i : Fin 4) :
    shiftByteContribution i.val (x.extractLsb' (8 * i.val) 8).toNat amount tag =
      shiftOperation tag (byteChunk x i) amount := by
  have widen : BitVec.ofNat 32 (x.extractLsb' (8 * i.val) 8).toNat =
      (x.extractLsb' (8 * i.val) 8).setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := (x.extractLsb' (8 * i.val) 8).isLt; omega)
  rcases valid with rfl | rfl | rfl | rfl
  · change ((BitVec.ofNat 32 (x.extractLsb' (8 * i.val) 8).toNat).shiftLeft (8 * i.val)).shiftLeft amount =
      (byteChunk x i).shiftLeft amount
    rw [widen]
    rfl
  · change ((BitVec.ofNat 32 (x.extractLsb' (8 * i.val) 8).toNat).shiftLeft (8 * i.val)).ushiftRight amount =
      (byteChunk x i).ushiftRight amount
    rw [widen]
    rfl
  · change ((BitVec.ofNat 32 (x.extractLsb' (8 * i.val) 8).toNat).shiftLeft (8 * i.val)).sshiftRight amount =
      (byteChunk x i).sshiftRight amount
    rw [widen]
    rfl
  · rw [reverse rfl]
    change (BitVec.ofNat 32 (x.extractLsb' (8 * i.val) 8).toNat).shiftLeft (8 * (3 - i.val)) =
      RV.rev8 (byteChunk x i)
    rw [widen, rev8_bytes]
    fin_cases i <;> simp only [byteChunk]
    all_goals
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      interval_cases k
      all_goals
        simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
        norm_num

/-- Disjoint native byte contributions also assemble each half without carry. -/
theorem shift_contribution_halves (tag : Nat) (valid : tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 5)
    (x : BitVec 32) (amount : Nat) (reverse : tag = 5 → amount = 0) (half : Fin 2) :
    ((shiftOperation tag x amount).extractLsb' (16 * half.val) 16).toNat =
      ((shiftByteContribution 0 (x.extractLsb' 0 8).toNat amount tag).extractLsb' (16 * half.val) 16).toNat +
      ((shiftByteContribution 1 (x.extractLsb' 8 8).toNat amount tag).extractLsb' (16 * half.val) 16).toNat +
      ((shiftByteContribution 2 (x.extractLsb' 16 8).toNat amount tag).extractLsb' (16 * half.val) 16).toNat +
      ((shiftByteContribution 3 (x.extractLsb' 24 8).toNat amount tag).extractLsb' (16 * half.val) 16).toNat := by
  let f := fun y : BitVec 32 => ((shiftOperation tag y amount).extractLsb' (16 * half.val) 16).setWidth 32
  have zero : f 0 = 0 := by
    rcases valid with rfl | rfl | rfl | rfl <;>
      simp [f, shiftOperation, rev8_bytes]
  have intersection : ∀ a b, f (a &&& b) = f a &&& f b := by
    intro a b
    rcases valid with rfl | rfl | rfl | rfl
    · simp [f, shiftOperation, BitVec.shiftLeft_and_distrib, BitVec.extractLsb'_and]
    · simp [f, shiftOperation, BitVec.ushiftRight_and_distrib, BitVec.extractLsb'_and]
    · simp [f, shiftOperation, BitVec.sshiftRight_and_distrib, BitVec.extractLsb'_and]
    · simp only [f, shiftOperation, Nat.reduceEqDiff, ite_false, rev8_bytes]
      fin_cases half
      all_goals
        apply BitVec.eq_of_getLsbD_eq
        intro k hk
        interval_cases k
        all_goals
          simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
            BitVec.getLsbD_append, BitVec.getLsbD_and]
          norm_num
  have union : ∀ a b, f (a ||| b) = f a ||| f b := by
    intro a b
    rcases valid with rfl | rfl | rfl | rfl
    · simp [f, shiftOperation, BitVec.shiftLeft_or_distrib, BitVec.extractLsb'_or]
    · simp [f, shiftOperation, BitVec.ushiftRight_or_distrib, BitVec.extractLsb'_or]
    · simp [f, shiftOperation, BitVec.sshiftRight_or_distrib, BitVec.extractLsb'_or]
    · simp only [f, shiftOperation, Nat.reduceEqDiff, ite_false, rev8_bytes]
      fin_cases half
      all_goals
        apply BitVec.eq_of_getLsbD_eq
        intro k hk
        interval_cases k
        all_goals
          simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
            BitVec.getLsbD_append, BitVec.getLsbD_or]
          norm_num
  have combined := mapped_chunks_value f zero intersection union x
  simp only [f, BitVec.toNat_setWidth_of_le (by decide : 16 ≤ 32)] at combined
  have mapped (i : Fin 4) := (contribution_eq tag valid x amount reverse i).symm
  simp only [mapped] at combined
  exact combined

theorem shift_contributions_value (tag : Nat) (valid : tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 5)
    (x : BitVec 32) (amount : Nat) (reverse : tag = 5 → amount = 0) :
    (shiftOperation tag x amount).toNat =
      (shiftByteContribution 0 (x.extractLsb' 0 8).toNat amount tag).toNat +
      (shiftByteContribution 1 (x.extractLsb' 8 8).toNat amount tag).toNat +
      (shiftByteContribution 2 (x.extractLsb' 16 8).toNat amount tag).toNat +
      (shiftByteContribution 3 (x.extractLsb' 24 8).toNat amount tag).toNat := by
  have chunk (i : Fin 4) : byteChunk x i =
      (BitVec.ofNat 32 (x.extractLsb' (8 * i.val) 8).toNat).shiftLeft (8 * i.val) := by
    unfold byteChunk
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by have := (x.extractLsb' (8 * i.val) 8).isLt; omega)).symm
  rcases valid with rfl | rfl | rfl | rfl
  · simpa [shiftOperation, shiftByteContribution, chunk] using shiftLeft_chunks_value x amount
  · simpa [shiftOperation, shiftByteContribution, chunk] using ushiftRight_chunks_value x amount
  · simpa [shiftOperation, shiftByteContribution, chunk] using sshiftRight_chunks_value x amount
  · rw [reverse rfl]
    have b0 := (x.extractLsb' 0 8).isLt
    have b1 := (x.extractLsb' 8 8).isLt
    have b2 := (x.extractLsb' 16 8).isLt
    have b3 := (x.extractLsb' 24 8).isLt
    change (RV.rev8 x).toNat =
      ((BitVec.ofNat 32 (x.extractLsb' 0 8).toNat) <<< 24).toNat +
      ((BitVec.ofNat 32 (x.extractLsb' 8 8).toNat) <<< 16).toNat +
      ((BitVec.ofNat 32 (x.extractLsb' 16 8).toNat) <<< 8).toNat +
      ((BitVec.ofNat 32 (x.extractLsb' 24 8).toNat) <<< 0).toNat
    rw [rev8_value]
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    norm_num only [Nat.reducePow] at *
    omega

/-- Low-byte truncation equals the architectural low-five-bit amount. -/
theorem low_byte_shift_amount (x : BitVec 32) :
    (x.extractLsb' 0 8).toNat % 32 = (x.extractLsb' 0 5).toNat := by
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  norm_num only [Nat.reducePow, Nat.div_one]
  exact Nat.mod_mod_of_dvd _ (by decide)

end Airbender.Verification
