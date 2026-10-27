import Slop.ISA.Equiv.DecMopR1
import Slop.ISA.Equiv.DecMopR2
import Slop.ISA.Equiv.DecMopR3

/-! Sail's decoder on every word our `RV.decodeMopR` accepts: the case of `N` by its bits (`DecMopR1` … `3`). -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 400000

/-- `N` as a number (all 32 cases checked). -/
theorem toNat_mopN : ∀ (a : BitVec 1) (b c : BitVec 2), (a ++ b ++ c).toNat = a.toNat * 16 + b.toNat * 4 + c.toNat := by
  decide

theorem dec_mopr (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) {i : RV.Instr} (h : RV.decodeMopR w (w.extractLsb' 7 5) (w.extractLsb' 15 5) = some i) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail i) σ := by
  unfold RV.decodeMopR at h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨c31, c28, c22, hn⟩ := hc
  cases h
  have h4 : Bits w 22 4 7 := by unfold Bits; rw [← BitVec.extractLsb'_toNat, c22]; rfl
  have t31 : (w.extractLsb' 31 1).toNat = 1 := by rw [c31]; rfl
  have t28 : (w.extractLsb' 28 2).toNat = 0 := by rw [c28]; rfl
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at t31 t28
  have hk : Bits w 26 6 (w.toNat / 2 ^ 26 % 64) := by unfold Bits; rw [Nat.shiftRight_eq_div_pow]; rfl
  have hl : Bits w 20 2 (w.toNat / 2 ^ 20 % 4) := by unfold Bits; rw [Nat.shiftRight_eq_div_pow]; rfl
  -- `N` = 28 … 31 only with `rd = x0`
  have h5 : w.toNat / 2 ^ 26 % 64 = 51 → Bits w 7 5 0 := by
    intro e
    rcases hn with hn | hn | hn | hn | hn
    rotate_left 4
    · unfold Bits; rw [← BitVec.extractLsb'_toNat, hn]; rfl
    all_goals
      exfalso
      have := congrArg BitVec.toNat hn
      rw [toNat_mopN] at this
      simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at this
      simp only [BitVec.toNat_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceMod] at this
      norm_num at this
      omega
  rcases (by omega : w.toNat / 2 ^ 26 % 64 = 32 ∨ w.toNat / 2 ^ 26 % 64 = 33 ∨ w.toNat / 2 ^ 26 % 64 = 34 ∨
      w.toNat / 2 ^ 26 % 64 = 35 ∨ w.toNat / 2 ^ 26 % 64 = 48 ∨ w.toNat / 2 ^ 26 % 64 = 49 ∨
      w.toNat / 2 ^ 26 % 64 = 50 ∨ w.toNat / 2 ^ 26 % 64 = 51) with e | e | e | e | e | e | e | e
  all_goals rw [e] at hk
  · exact dec_mopr_0 w σ hs h0 h1 hk h4
  · exact dec_mopr_1 w σ hs h0 h1 hk h4
  · exact dec_mopr_2 w σ hs h0 h1 hk h4
  · exact dec_mopr_3 w σ hs h0 h1 hk h4
  · exact dec_mopr_4 w σ hs h0 h1 hk h4
  · exact dec_mopr_5 w σ hs h0 h1 hk h4
  · exact dec_mopr_6 w σ hs h0 h1 hk h4
  · have hrd0 := h5 e
    rcases (by omega : w.toNat / 2 ^ 20 % 4 = 0 ∨ w.toNat / 2 ^ 20 % 4 = 1 ∨ w.toNat / 2 ^ 20 % 4 = 2 ∨
      w.toNat / 2 ^ 20 % 4 = 3) with f | f | f | f
    all_goals rw [f] at hl
    · exact dec_mopr_7_0 w σ hs h0 h1 hk hl h4 hrd0
    · exact dec_mopr_7_1 w σ hs h0 h1 hk hl h4 hrd0
    · exact dec_mopr_7_2 w σ hs h0 h1 hk hl h4 hrd0
    · exact dec_mopr_7_3 w σ hs h0 h1 hk hl h4 hrd0

end Slop.Equiv
