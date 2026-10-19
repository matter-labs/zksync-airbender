import Airbender.Proofs.Tables.SllLowParts

namespace Airbender.Verification.SllLowProofs
open Setup Setup.Proofs NativeSllLow
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

theorem outputs_part4 : checkBlocks sllLowHighOutput 327680 part4 = true := by
  rw [part4_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside := i.isLt
    have sh : (327680 + i.val) / 65536 = 5 := by omega
    have value : (((327680 + i.val) % 65536) * 32 / 65536) % 65536 = 0 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 0 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (329728 + i.val) / 65536 = 5 := by omega
    have value : (((329728 + i.val) % 65536) * 32 / 65536) % 65536 = 1 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 1 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (331776 + i.val) / 65536 = 5 := by omega
    have value : (((331776 + i.val) % 65536) * 32 / 65536) % 65536 = 2 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 2 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (333824 + i.val) / 65536 = 5 := by omega
    have value : (((333824 + i.val) % 65536) * 32 / 65536) % 65536 = 3 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 3 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (335872 + i.val) / 65536 = 5 := by omega
    have value : (((335872 + i.val) % 65536) * 32 / 65536) % 65536 = 4 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 4 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (337920 + i.val) / 65536 = 5 := by omega
    have value : (((337920 + i.val) % 65536) * 32 / 65536) % 65536 = 5 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 5 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (339968 + i.val) / 65536 = 5 := by omega
    have value : (((339968 + i.val) % 65536) * 32 / 65536) % 65536 = 6 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 6 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (342016 + i.val) / 65536 = 5 := by omega
    have value : (((342016 + i.val) % 65536) * 32 / 65536) % 65536 = 7 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 7 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (344064 + i.val) / 65536 = 5 := by omega
    have value : (((344064 + i.val) % 65536) * 32 / 65536) % 65536 = 8 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 8 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (346112 + i.val) / 65536 = 5 := by omega
    have value : (((346112 + i.val) % 65536) * 32 / 65536) % 65536 = 9 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 9 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (348160 + i.val) / 65536 = 5 := by omega
    have value : (((348160 + i.val) % 65536) * 32 / 65536) % 65536 = 10 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 10 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (350208 + i.val) / 65536 = 5 := by omega
    have value : (((350208 + i.val) % 65536) * 32 / 65536) % 65536 = 11 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 11 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (352256 + i.val) / 65536 = 5 := by omega
    have value : (((352256 + i.val) % 65536) * 32 / 65536) % 65536 = 12 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 12 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (354304 + i.val) / 65536 = 5 := by omega
    have value : (((354304 + i.val) % 65536) * 32 / 65536) % 65536 = 13 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 13 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (356352 + i.val) / 65536 = 5 := by omega
    have value : (((356352 + i.val) % 65536) * 32 / 65536) % 65536 = 14 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 14 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (358400 + i.val) / 65536 = 5 := by omega
    have value : (((358400 + i.val) % 65536) * 32 / 65536) % 65536 = 15 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 15 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (360448 + i.val) / 65536 = 5 := by omega
    have value : (((360448 + i.val) % 65536) * 32 / 65536) % 65536 = 16 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 16 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (362496 + i.val) / 65536 = 5 := by omega
    have value : (((362496 + i.val) % 65536) * 32 / 65536) % 65536 = 17 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 17 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (364544 + i.val) / 65536 = 5 := by omega
    have value : (((364544 + i.val) % 65536) * 32 / 65536) % 65536 = 18 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 18 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (366592 + i.val) / 65536 = 5 := by omega
    have value : (((366592 + i.val) % 65536) * 32 / 65536) % 65536 = 19 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 19 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (368640 + i.val) / 65536 = 5 := by omega
    have value : (((368640 + i.val) % 65536) * 32 / 65536) % 65536 = 20 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 20 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (370688 + i.val) / 65536 = 5 := by omega
    have value : (((370688 + i.val) % 65536) * 32 / 65536) % 65536 = 21 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 21 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (372736 + i.val) / 65536 = 5 := by omega
    have value : (((372736 + i.val) % 65536) * 32 / 65536) % 65536 = 22 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 22 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (374784 + i.val) / 65536 = 5 := by omega
    have value : (((374784 + i.val) % 65536) * 32 / 65536) % 65536 = 23 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 23 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (376832 + i.val) / 65536 = 5 := by omega
    have value : (((376832 + i.val) % 65536) * 32 / 65536) % 65536 = 24 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 24 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (378880 + i.val) / 65536 = 5 := by omega
    have value : (((378880 + i.val) % 65536) * 32 / 65536) % 65536 = 25 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 25 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (380928 + i.val) / 65536 = 5 := by omega
    have value : (((380928 + i.val) % 65536) * 32 / 65536) % 65536 = 26 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 26 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (382976 + i.val) / 65536 = 5 := by omega
    have value : (((382976 + i.val) % 65536) * 32 / 65536) % 65536 = 27 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 27 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (385024 + i.val) / 65536 = 5 := by omega
    have value : (((385024 + i.val) % 65536) * 32 / 65536) % 65536 = 28 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 28 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (387072 + i.val) / 65536 = 5 := by omega
    have value : (((387072 + i.val) % 65536) * 32 / 65536) % 65536 = 29 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 29 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (389120 + i.val) / 65536 = 5 := by omega
    have value : (((389120 + i.val) % 65536) * 32 / 65536) % 65536 = 30 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 30 0 i.val inside
  · intro i
    have inside := i.isLt
    have sh : (391168 + i.val) / 65536 = 5 := by omega
    have value : (((391168 + i.val) % 65536) * 32 / 65536) % 65536 = 31 := by omega
    rw [sllLowHighOutput,sh]
    norm_num only
    rw [value]
    simpa using affine_get 2048 31 0 i.val inside

end Airbender.Verification.SllLowProofs
