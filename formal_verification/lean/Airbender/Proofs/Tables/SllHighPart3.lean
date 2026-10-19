import Airbender.Proofs.Tables.SllHighParts

namespace Airbender.Verification.SllHighProofs
open Setup Setup.Proofs NativeSllHigh
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

theorem outputs_part3 : checkBlocks sllHighOutput 327680 part3 = true := by
  rw [part3_shape]
  simp only [checkBlocks_cons_iff,checkBlocks_nil,and_true,Block.length,
    Nat.reduceAdd]
  repeat' apply And.intro
  · intro i
    have inside := i.isLt
    have shift : (327680 + i.val) / 65536 = 5 := by omega
    have result : (((327680 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (329728 + i.val) / 65536 = 5 := by omega
    have result : (((329728 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (331776 + i.val) / 65536 = 5 := by omega
    have result : (((331776 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (333824 + i.val) / 65536 = 5 := by omega
    have result : (((333824 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (335872 + i.val) / 65536 = 5 := by omega
    have result : (((335872 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (337920 + i.val) / 65536 = 5 := by omega
    have result : (((337920 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (339968 + i.val) / 65536 = 5 := by omega
    have result : (((339968 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (342016 + i.val) / 65536 = 5 := by omega
    have result : (((342016 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (344064 + i.val) / 65536 = 5 := by omega
    have result : (((344064 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (346112 + i.val) / 65536 = 5 := by omega
    have result : (((346112 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (348160 + i.val) / 65536 = 5 := by omega
    have result : (((348160 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (350208 + i.val) / 65536 = 5 := by omega
    have result : (((350208 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (352256 + i.val) / 65536 = 5 := by omega
    have result : (((352256 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (354304 + i.val) / 65536 = 5 := by omega
    have result : (((354304 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (356352 + i.val) / 65536 = 5 := by omega
    have result : (((356352 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (358400 + i.val) / 65536 = 5 := by omega
    have result : (((358400 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (360448 + i.val) / 65536 = 5 := by omega
    have result : (((360448 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (362496 + i.val) / 65536 = 5 := by omega
    have result : (((362496 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (364544 + i.val) / 65536 = 5 := by omega
    have result : (((364544 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (366592 + i.val) / 65536 = 5 := by omega
    have result : (((366592 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (368640 + i.val) / 65536 = 5 := by omega
    have result : (((368640 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (370688 + i.val) / 65536 = 5 := by omega
    have result : (((370688 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (372736 + i.val) / 65536 = 5 := by omega
    have result : (((372736 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (374784 + i.val) / 65536 = 5 := by omega
    have result : (((374784 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (376832 + i.val) / 65536 = 5 := by omega
    have result : (((376832 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (378880 + i.val) / 65536 = 5 := by omega
    have result : (((378880 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (380928 + i.val) / 65536 = 5 := by omega
    have result : (((380928 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (382976 + i.val) / 65536 = 5 := by omega
    have result : (((382976 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (385024 + i.val) / 65536 = 5 := by omega
    have result : (((385024 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (387072 + i.val) / 65536 = 5 := by omega
    have result : (((387072 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (389120 + i.val) / 65536 = 5 := by omega
    have result : (((389120 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside
  · intro i
    have inside := i.isLt
    have shift : (391168 + i.val) / 65536 = 5 := by omega
    have result : (((391168 + i.val) % 65536) * 32) % 65536 = 32 * i.val := by omega
    rw [sllHighOutput,shift]
    norm_num only
    rw [result]
    simpa using affine_get 2048 0 32 i.val inside

end Airbender.Verification.SllHighProofs
