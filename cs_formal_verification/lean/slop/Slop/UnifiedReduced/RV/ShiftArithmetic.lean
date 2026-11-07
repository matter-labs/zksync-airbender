import Slop.ShiftBinop.Lookups
import Human.ISA.RV32
import Mathlib.Tactic.IntervalCases

/-! Sail-free copy of the shift assembly (`ShiftBinop/Arithmetic.lean`, `Arithmetic/ShiftAssembly.lean`): the REV8
    branch of `shiftOperation` is our spec's `RV.rev8` instead of the Sail library's byte loop. -/

namespace Airbender.Verification.RVShift
open Airbender.Arithmetic Airbender.Verification
set_option maxRecDepth 16384

def shiftOperation (tag : Nat) (x : BitVec 32) (amount : Nat) : BitVec 32 :=
  if tag = 1 then x.shiftLeft amount else if tag = 2 then x.ushiftRight amount
  else if tag = 3 then x.sshiftRight amount else RV.rev8 x

theorem rev8_bytes (x : BitVec 32) : RV.rev8 x =
    ((x.extractLsb' 0 8) ++ (x.extractLsb' 8 8)) ++ ((x.extractLsb' 16 8) ++ (x.extractLsb' 24 8)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [RV.rev8, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases k <;> simp

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

theorem shift_assembly (tag : Nat) (valid : tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 5)
    (x : BitVec 32) (amount : Nat) (reverse : tag = 5 → amount = 0)
    (parts : Fin 4 → Fin 4 → Nat) (output : Word)
    (bytes : ∀ i j : Fin 4, parts i j =
      ((shiftByteContribution i.val (x.extractLsb' (8 * i.val) 8).toNat amount tag).extractLsb' (8 * j.val) 8).toNat)
    (low : output.lo = parts 0 0 + 256 * parts 0 1 + parts 1 0 + 256 * parts 1 1 +
      parts 2 0 + 256 * parts 2 1 + parts 3 0 + 256 * parts 3 1)
    (high : output.hi = parts 0 2 + 256 * parts 0 3 + parts 1 2 + 256 * parts 1 3 +
      parts 2 2 + 256 * parts 2 3 + parts 3 2 + 256 * parts 3 3) :
    output.toBitVec = shiftOperation tag x amount := by
  let contribution (i : Fin 4) := shiftByteContribution i.val (x.extractLsb' (8 * i.val) 8).toNat amount tag
  have rebuild (i : Fin 4) :
      parts i 0 + 256 * parts i 1 + 65536 * parts i 2 + 16777216 * parts i 3 = (contribution i).toNat := by
    rw [bytes i 0, bytes i 1, bytes i 2, bytes i 3]
    exact (bytes_value (contribution i)).symm
  have value : output.value = (contribution 0).toNat + (contribution 1).toNat +
      (contribution 2).toNat + (contribution 3).toNat := by
    rw [Word.value, low, high, ← rebuild 0, ← rebuild 1, ← rebuild 2, ← rebuild 3]
    dsimp [limbBase]
    ring
  have combined := shift_contributions_value tag valid x amount reverse
  change (shiftOperation tag x amount).toNat =
    (contribution 0).toNat + (contribution 1).toNat + (contribution 2).toNat + (contribution 3).toNat at combined
  apply BitVec.eq_of_toNat_eq
  change output.value % wordModulus = _
  rw [value, ← combined]
  exact Nat.mod_eq_of_lt (shiftOperation tag x amount).isLt

end Airbender.Verification.RVShift
