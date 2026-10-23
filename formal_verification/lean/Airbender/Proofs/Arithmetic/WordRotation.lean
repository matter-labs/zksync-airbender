import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases
import Airbender.Proofs.Arithmetic.Bytes

namespace Airbender.Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem rotateRight_and (x y : BitVec 32) (amount : Nat) :
    (x &&& y).rotateRight amount = x.rotateRight amount &&& y.rotateRight amount := by
  ext i bound
  simp only [BitVec.getElem_rotateRight, BitVec.getElem_and]
  split_ifs <;> rfl

theorem rotateRight_or (x y : BitVec 32) (amount : Nat) :
    (x ||| y).rotateRight amount = x.rotateRight amount ||| y.rotateRight amount := by
  ext i bound
  simp only [BitVec.getElem_rotateRight, BitVec.getElem_or]
  split_ifs <;> rfl

theorem rotated_chunks_limb (x : BitVec 32) (amount start : Nat) :
    ((x.rotateRight amount).extractLsb' start 16).toNat =
      (((byteChunk x 0).rotateRight amount).extractLsb' start 16).toNat +
      (((byteChunk x 1).rotateRight amount).extractLsb' start 16).toNat +
      (((byteChunk x 2).rotateRight amount).extractLsb' start 16).toNat +
      (((byteChunk x 3).rotateRight amount).extractLsb' start 16).toNat := by
  have normalized (value : BitVec 16) : (value.setWidth 32).toNat = value.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
    have := value.isLt
    omega
  have mapped := mapped_chunks_value
    (fun value => ((value.rotateRight amount).extractLsb' start 16).setWidth 32)
    (by simp [BitVec.rotateRight_def])
    (fun a b => by rw [rotateRight_and, BitVec.extractLsb'_and, BitVec.setWidth_and])
    (fun a b => by rw [rotateRight_or, BitVec.extractLsb'_or, BitVec.setWidth_or]) x
  simpa only [normalized] using mapped

def rotatedByte32 (x : BitVec 32) (kind : Fin 4) (i : Fin 4) : BitVec 32 :=
  ((x.extractLsb' (8 * i.val) 8).setWidth 32).rotateRight #[16, 12, 8, 7][kind.val]!

theorem rotated_chunk_pair (x : BitVec 32) (kind : Fin 4) (i : Fin 4) (limb : Fin 2) :
    ((byteChunk x i).rotateRight #[16, 12, 8, 7][kind.val]!).extractLsb' (16 * limb.val) 16 =
      (rotatedByte32 x kind i).extractLsb' (8 * ((1 + 2 * limb.val + 4 - i.val) % 4)) 8 ++
      (rotatedByte32 x kind i).extractLsb' (8 * ((2 * limb.val + 4 - i.val) % 4)) 8 := by
  fin_cases kind <;> fin_cases i <;> fin_cases limb
  all_goals dsimp [rotatedByte32, byteChunk]
  all_goals
    apply BitVec.eq_of_getLsbD_eq
    intro j bound
    rw [BitVec.getLsbD_append]
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    interval_cases j
    all_goals simp

theorem sum_four (f : Fin 4 → Nat) : (∑ i : Fin 4, f i) = f 0 + f 1 + f 2 + f 3 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + f 3)) = _
  omega

theorem rotated_limb_bytes (x : BitVec 32) (kind : Fin 4) (limb : Fin 2) :
    ((x.rotateRight #[16, 12, 8, 7][kind.val]!).extractLsb' (16 * limb.val) 16).toNat =
      ∑ i : Fin 4,
        (((rotatedByte32 x kind i).extractLsb' (8 * ((2 * limb.val + 4 - i.val) % 4)) 8).toNat +
        256 * ((rotatedByte32 x kind i).extractLsb' (8 * ((1 + 2 * limb.val + 4 - i.val) % 4)) 8).toNat) := by
  have pair (i : Fin 4) :
      (((byteChunk x i).rotateRight #[16, 12, 8, 7][kind.val]!).extractLsb' (16 * limb.val) 16).toNat =
        ((rotatedByte32 x kind i).extractLsb' (8 * ((2 * limb.val + 4 - i.val) % 4)) 8).toNat +
        256 * ((rotatedByte32 x kind i).extractLsb' (8 * ((1 + 2 * limb.val + 4 - i.val) % 4)) 8).toNat := by
    rw [rotated_chunk_pair, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt
      (((rotatedByte32 x kind i).extractLsb' (8 * ((2 * limb.val + 4 - i.val) % 4)) 8).isLt), Nat.shiftLeft_eq]
    omega
  have chunks := rotated_chunks_limb x #[16, 12, 8, 7][kind.val]! (16 * limb.val)
  rw [pair 0, pair 1, pair 2, pair 3] at chunks
  rw [sum_four]
  omega

end Airbender.Arithmetic
