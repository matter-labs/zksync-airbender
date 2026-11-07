import Airbender.Proofs.Keccak.SplitThetaCallAddresses
import Airbender.Proofs.Keccak.SplitChiLaneHalves

namespace Airbender.Keccak.Split.Native.Proofs
open Arithmetic Trace
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Each actual theta read token retains its complete raw native limb pair. -/
theorem theta_read_word (cached high : Bool) (w : Nat → ZMod babyBearModulus) (lane : Fin 7) :
    (readToken w (thetaLanePort cached lane high)).word =
      Word.mk (thetaLaneLimb cached false w lane (if high then 2 else 0)).val
        (thetaLaneLimb cached false w lane (if high then 3 else 1)).val := by
  change Word.mk (Nat.unpair ((thetaLanePort cached lane high).readCode w)).1
    (Nat.unpair ((thetaLanePort cached lane high).readCode w)).2 = _
  have code := theta_lane_port_values cached false high w lane
  change (thetaLanePort cached lane high).readCode w = Nat.pair _ _ at code
  rw [code, Nat.unpair_pair]

/-- Initialized bounds on both actual words bound every lane limb, including old scratch data. -/
theorem theta_read_limb_bounds (cached : Bool) (w : Nat → ZMod babyBearModulus) (lane : Fin 7)
    (bounded : ∀ high : Bool, (readToken w (thetaLanePort cached lane high)).word.Bounded) :
    ∀ limb : Fin 4, (thetaLaneLimb cached false w lane limb).val < 65536 := by
  have low := bounded false
  have high := bounded true
  rw [theta_read_word] at low high
  change (thetaLaneLimb cached false w lane 0).val < 65536 ∧
    (thetaLaneLimb cached false w lane 1).val < 65536 at low
  change (thetaLaneLimb cached false w lane 2).val < 65536 ∧
    (thetaLaneLimb cached false w lane 3).val < 65536 at high
  intro limb
  fin_cases limb
  · exact low.1
  · exact low.2
  · exact high.1
  · exact high.2

/-- Initialized actual read words give a complete bounded reference input lane. -/
theorem theta_read_lane_bound (cached : Bool) (w : Nat → ZMod babyBearModulus) (lane : Fin 7)
    (bounded : ∀ high : Bool, (readToken w (thetaLanePort cached lane high)).word.Bounded) :
    thetaLaneValue cached false w lane < 2 ^ 64 := by
  have bounds := theta_read_limb_bounds cached w lane bounded
  have h0 := bounds 0; have h1 := bounds 1; have h2 := bounds 2; have h3 := bounds 3
  change (thetaLaneLimb cached false w lane 0).val + 65536 *
    ((thetaLaneLimb cached false w lane 1).val + 65536 *
      ((thetaLaneLimb cached false w lane 2).val + 65536 * (thetaLaneLimb cached false w lane 3).val)) < 2 ^ 64
  norm_num only [Nat.reducePow]
  omega

/-- Actual theta port words equal the reference halves when their low limbs are bounded. -/
theorem theta_lane_port_half (cached writing high : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 7)
    (low : (thetaLaneLimb cached writing w lane 0).val < 65536)
    (next : (thetaLaneLimb cached writing w lane 1).val < 65536) :
    Call.half (thetaLaneValue cached writing w lane) high = memoryWord
      (if writing then (thetaLanePort cached lane high).writeCode w
        else (thetaLanePort cached lane high).readCode w) := by
  rw [theta_lane_port_values]
  unfold memoryWord
  rw [Nat.unpair_pair]
  unfold thetaLaneValue packLane
  norm_num only [Nat.reducePow]
  cases high
  · exact chi5_four_limb_halves low next false
  · exact chi5_four_limb_halves low next true

/-- Native state writes and readonly refreshes retain bounded limbs from the exact initialized inputs. -/
theorem theta_all_write_limb_bounds (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (column : Fin 5)
    (flags : ∀ selected : Fin 5, thetaColumnFlag cached w selected = if selected.val = column.val then 1 else 0)
    (bounded : ∀ (lane : Fin 7) (high : Bool), (readToken w (thetaLanePort cached lane high)).word.Bounded)
    (lane : Fin 7) (limb : Fin 4) : (thetaLaneLimb cached true w lane limb).val < 65536 := by
  by_cases active : lane.val < 5
  · exact (theta_write_limb_value cached w holds column ⟨lane.val, active⟩ limb flags).1
  · let readonly : Fin 2 := ⟨lane.val - 5, by omega⟩
    have same : (⟨5 + readonly.val, by omega⟩ : Fin 7) = lane := by
      apply Fin.ext
      dsimp [readonly]
      omega
    have value := theta_readonly_limb cached w readonly limb
    rw [same] at value
    rw [value]
    exact theta_read_limb_bounds cached w lane (bounded lane) limb

/-- Both actual written theta/rho words have their exact reference output halves. -/
theorem theta_written_port_half (cached high : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (column : Fin 5)
    (flags : ∀ selected : Fin 5, thetaColumnFlag cached w selected = if selected.val = column.val then 1 else 0)
    (bounded : ∀ (lane : Fin 7) (high : Bool), (readToken w (thetaLanePort cached lane high)).word.Bounded)
    (lane : Fin 7) :
    Call.half (thetaLaneValue cached true w lane) high =
      memoryWord ((thetaLanePort cached lane high).writeCode w) := by
  exact theta_lane_port_half cached true high w lane
    (theta_all_write_limb_bounds cached w holds column flags bounded lane 0)
    (theta_all_write_limb_bounds cached w holds column flags bounded lane 1)

end Airbender.Keccak.Split.Native.Proofs
