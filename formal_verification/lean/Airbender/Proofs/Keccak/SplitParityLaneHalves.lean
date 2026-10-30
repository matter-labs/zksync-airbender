import Airbender.Proofs.Keccak.SplitParityCallAddresses
import Airbender.Proofs.Keccak.SplitChiLaneHalves

namespace Airbender.Keccak.Split.Native.Proofs
open Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
variable [Fact babyBearModulus.Prime]

/-- Each actual parity read token retains its complete raw native limb pair. -/
theorem parity_read_word (cached high : Bool) (w : Nat → ZMod babyBearModulus) (lane : Fin 6) :
    (readToken w (parityLanePort cached lane high)).word =
      Word.mk (parityLaneLimb cached false w lane (if high then 2 else 0)).val
        (parityLaneLimb cached false w lane (if high then 3 else 1)).val := by
  change Word.mk (Nat.unpair ((parityLanePort cached lane high).readCode w)).1
    (Nat.unpair ((parityLanePort cached lane high).readCode w)).2 = _
  have code := parity_lane_port_values cached false high w lane
  change (parityLanePort cached lane high).readCode w = Nat.pair _ _ at code
  rw [code, Nat.unpair_pair]

/-- Initialized bounds on both actual words bound every lane limb, including old scratch data. -/
theorem parity_read_limb_bounds (cached : Bool) (w : Nat → ZMod babyBearModulus) (lane : Fin 6)
    (bounded : ∀ high : Bool, (readToken w (parityLanePort cached lane high)).word.Bounded) :
    ∀ limb : Fin 4, (parityLaneLimb cached false w lane limb).val < 65536 := by
  have low := bounded false
  have high := bounded true
  rw [parity_read_word] at low high
  change (parityLaneLimb cached false w lane 0).val < 65536 ∧
    (parityLaneLimb cached false w lane 1).val < 65536 at low
  change (parityLaneLimb cached false w lane 2).val < 65536 ∧
    (parityLaneLimb cached false w lane 3).val < 65536 at high
  intro limb
  fin_cases limb
  · exact low.1
  · exact low.2
  · exact high.1
  · exact high.2

/-- Initialized actual read words give a complete bounded reference input lane. -/
theorem parity_read_lane_bound (cached : Bool) (w : Nat → ZMod babyBearModulus) (lane : Fin 6)
    (bounded : ∀ high : Bool, (readToken w (parityLanePort cached lane high)).word.Bounded) :
    parityLaneValue cached false w lane < 2 ^ 64 := by
  have bounds := parity_read_limb_bounds cached w lane bounded
  have h0 := bounds 0; have h1 := bounds 1; have h2 := bounds 2; have h3 := bounds 3
  unfold parityLaneValue packFourChunks
  norm_num only [Nat.reducePow]
  omega

/-- Actual parity port words equal the reference halves when their low limbs are bounded. -/
theorem parity_lane_port_half (cached writing high : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 6)
    (low : (parityLaneLimb cached writing w lane 0).val < 65536)
    (next : (parityLaneLimb cached writing w lane 1).val < 65536) :
    Call.half (parityLaneValue cached writing w lane) high = memoryWord
      (if writing then (parityLanePort cached lane high).writeCode w
        else (parityLanePort cached lane high).readCode w) := by
  rw [parity_lane_port_values]
  unfold memoryWord
  rw [Nat.unpair_pair]
  unfold parityLaneValue packFourChunks
  norm_num only [Nat.reducePow]
  cases high
  · exact chi5_four_limb_halves low next false
  · exact chi5_four_limb_halves low next true

/-- Both actual written parity words have their exact reference output halves. -/
theorem parity_written_port_half (cached high : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (lane : Fin 6) :
    Call.half (parityLaneValue cached true w lane) high =
      memoryWord ((parityLanePort cached lane high).writeCode w) := by
  exact parity_lane_port_half cached true high w lane
    (parity_write_limb_value cached w holds lane 0).1 (parity_write_limb_value cached w holds lane 1).1

end Airbender.Keccak.Split.Native.Proofs
