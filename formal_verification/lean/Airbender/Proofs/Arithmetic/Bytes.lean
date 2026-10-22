import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Arithmetic.Word
import Mathlib.Data.Nat.Bitwise

namespace Airbender.Arithmetic

/-- Reassemble four native bytes. Shared by byte-oriented circuit families. -/
theorem bytes_value (x : BitVec 32) :
    x.toNat = (x.extractLsb' 0 8).toNat + 256 * (x.extractLsb' 8 8).toNat +
      65536 * (x.extractLsb' 16 8).toNat + 16777216 * (x.extractLsb' 24 8).toNat := by
  have bound := x.isLt
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  norm_num only [Nat.reducePow, Nat.div_one] at *
  omega

theorem byte_pair_value {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 65536)
    (a b c : ZMod p) (ha : a.val < 256) (hb : b.val < 256)
    (equation : a + 256 * b = c) : c.val = a.val + 256 * b.val := by
  rw [← equation, ZMod.val_add, ZMod.val_mul]
  norm_num only [ZMod.val_natCast, ZMod.val_ofNat]
  rw [Nat.mod_eq_of_lt (show 256 < p by omega),
    Nat.mod_eq_of_lt (show 256 * b.val < p by omega),
    Nat.mod_eq_of_lt (show a.val + 256 * b.val < p by omega)]

/-- Disjoint bit sets add without carries. -/
theorem or_eq_add_of_disjoint (m n : Nat) (h : m &&& n = 0) : m ||| n = m + n := by
  induction m using Nat.binaryRec generalizing n with
  | zero => simp
  | bit b m ih =>
    induction n using Nat.binaryRec with
    | zero => simp
    | bit c n _ =>
      rw [Nat.land_bit] at h
      have upper : m &&& n = 0 := by
        cases b <;> cases c <;> simp [Nat.bit_val] at h <;> omega
      rw [Nat.lor_bit, ih n upper]
      cases b <;> cases c <;> simp [Nat.bit_val] at h ⊢ <;> omega

theorem bitvec_or_value {n : Nat} {a b : BitVec n} (h : a &&& b = 0) :
    (a ||| b).toNat = a.toNat + b.toNat := by
  apply or_eq_add_of_disjoint
  simpa using congrArg BitVec.toNat h

def byteChunk (x : BitVec 32) (i : Fin 4) : BitVec 32 :=
  ((x.extractLsb' (8 * i.val) 8).setWidth 32).shiftLeft (8 * i.val)

private theorem chunk_bits (x : BitVec 32) (i : Fin 4) (k : Nat) (hk : k < 32) :
    (byteChunk x i)[k] = if 8 * i.val ≤ k ∧ k < 8 * i.val + 8 then x[k] else false := by
  by_cases lo : k < 8 * i.val
  · have before : ¬ 8 * i.val ≤ k := by omega
    simp [byteChunk, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getLsbD_extractLsb', lo, before]
  · have ge : 8 * i.val ≤ k := by omega
    have offset : 8 * i.val + (k - 8 * i.val) = k := by omega
    by_cases hi : k < 8 * i.val + 8
    · have inside : k - 8 * i.val < 8 := by omega
      simp [byteChunk, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
        lo, ge, hi, offset, inside, BitVec.getLsbD_eq_getElem, hk]
    · have outside : ¬ k - 8 * i.val < 8 := by omega
      simp [byteChunk, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
        BitVec.getLsbD_extractLsb', lo, ge, hi, outside]

theorem chunks_disjoint (x : BitVec 32) (i j : Fin 4) (different : i ≠ j) :
    byteChunk x i &&& byteChunk x j = 0 := by
  have ne : i.val ≠ j.val := by exact fun eq => different (Fin.ext eq)
  ext k hk
  simp only [BitVec.getElem_and, chunk_bits x i k hk, chunk_bits x j k hk]
  split_ifs
  all_goals solve | omega | simp_all

theorem chunks_or (x : BitVec 32) :
    (byteChunk x 0 ||| byteChunk x 1) ||| (byteChunk x 2 ||| byteChunk x 3) = x := by
  ext k hk
  simp only [BitVec.getElem_or, chunk_bits x 0 k hk, chunk_bits x 1 k hk,
    chunk_bits x 2 k hk, chunk_bits x 3 k hk]
  split_ifs <;> simp_all

/-- Bitwise maps preserving intersection and union preserve byte disjointness.
    This covers all three shifts, including arithmetic right shift. -/
theorem mapped_chunks_value (f : BitVec 32 → BitVec 32)
    (zero : f 0 = 0)
    (intersection : ∀ a b, f (a &&& b) = f a &&& f b)
    (union : ∀ a b, f (a ||| b) = f a ||| f b) (x : BitVec 32) :
    (f x).toNat = (f (byteChunk x 0)).toNat + (f (byteChunk x 1)).toNat +
      (f (byteChunk x 2)).toNat + (f (byteChunk x 3)).toNat := by
  have disjoint (i j : Fin 4) (ne : i ≠ j) :
      f (byteChunk x i) &&& f (byteChunk x j) = 0 := by
    rw [← intersection, chunks_disjoint x i j ne, zero]
  have pairs : (f (byteChunk x 0) ||| f (byteChunk x 1)) &&&
      (f (byteChunk x 2) ||| f (byteChunk x 3)) = 0 := by
    simp only [BitVec.and_or_distrib_left, BitVec.and_or_distrib_right,
      disjoint 0 2 (by decide), disjoint 1 2 (by decide),
      disjoint 0 3 (by decide), disjoint 1 3 (by decide)]
    rfl
  have combined := congrArg f (chunks_or x)
  rw [union, union, union] at combined
  rw [← combined, bitvec_or_value pairs,
    bitvec_or_value (disjoint 0 1 (by decide)), bitvec_or_value (disjoint 2 3 (by decide))]
  omega

theorem shiftLeft_chunks_value (x : BitVec 32) (amount : Nat) :
    (x.shiftLeft amount).toNat = ((byteChunk x 0).shiftLeft amount).toNat +
      ((byteChunk x 1).shiftLeft amount).toNat + ((byteChunk x 2).shiftLeft amount).toNat +
      ((byteChunk x 3).shiftLeft amount).toNat :=
  mapped_chunks_value (fun y => y.shiftLeft amount) (by simp)
    (fun a b => BitVec.shiftLeft_and_distrib a b amount) (fun a b => BitVec.shiftLeft_or_distrib a b amount) x

theorem ushiftRight_chunks_value (x : BitVec 32) (amount : Nat) :
    (x.ushiftRight amount).toNat = ((byteChunk x 0).ushiftRight amount).toNat +
      ((byteChunk x 1).ushiftRight amount).toNat + ((byteChunk x 2).ushiftRight amount).toNat +
      ((byteChunk x 3).ushiftRight amount).toNat :=
  mapped_chunks_value (fun y => y.ushiftRight amount) (by simp)
    (fun a b => BitVec.ushiftRight_and_distrib a b amount) (fun a b => BitVec.ushiftRight_or_distrib a b amount) x

theorem sshiftRight_chunks_value (x : BitVec 32) (amount : Nat) :
    (x.sshiftRight amount).toNat = ((byteChunk x 0).sshiftRight amount).toNat +
      ((byteChunk x 1).sshiftRight amount).toNat + ((byteChunk x 2).sshiftRight amount).toNat +
      ((byteChunk x 3).sshiftRight amount).toNat :=
  mapped_chunks_value (fun y => y.sshiftRight amount) (by simp)
    (fun a b => BitVec.sshiftRight_and_distrib a b amount) (fun a b => BitVec.sshiftRight_or_distrib a b amount) x

end Airbender.Arithmetic
