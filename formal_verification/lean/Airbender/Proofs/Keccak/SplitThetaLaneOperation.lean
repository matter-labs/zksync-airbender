import Airbender.Proofs.Keccak.SplitThetaOutputPacking
import Airbender.Proofs.Keccak.SplitThetaDOperation

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The four actual theta/rho memory limbs form one complete lane. -/
def thetaLaneValue (cached writing : Bool) (w : Nat → ZMod babyBearModulus) (lane : Fin 7) : Nat :=
  packLane (Vector.ofFn fun limb : Fin 4 => (thetaLaneLimb cached writing w lane limb).val)

/-- The two complete native parity-input lanes stay unchanged. -/
theorem theta_readonly_lane (cached : Bool) (w : Nat → ZMod babyBearModulus) (lane : Fin 2) :
    thetaLaneValue cached true w ⟨5 + lane.val, by omega⟩ =
      thetaLaneValue cached false w ⟨5 + lane.val, by omega⟩ := by
  unfold thetaLaneValue
  congr 1
  apply Vector.ext
  intro limb bound
  simpa only [Vector.getElem_ofFn] using congrArg ZMod.val (theta_readonly_limb cached w lane ⟨limb, bound⟩)

variable [Fact babyBearModulus.Prime]

/-- The actual state-read lane equals its eight complete queried bytes. -/
theorem theta_state_lane_bytes (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (lane : Fin 5) :
    thetaLaneValue cached false w ⟨lane.val, by omega⟩ =
      packByteLane (Vector.ofFn fun digit : Fin 8 => (thetaStateByte cached w lane digit).val) := by
  let bytes := Vector.ofFn fun digit : Fin 8 => (thetaStateByte cached w lane digit).val
  calc
    _ = packLane (Vector.ofFn fun limb : Fin 4 =>
        bytes[(⟨2 * limb.val, by omega⟩ : Fin 8)] +
          256 * bytes[(⟨2 * limb.val + 1, by omega⟩ : Fin 8)]) := by
      unfold thetaLaneValue
      congr 1
      apply Vector.ext
      intro limb bound
      simpa [bytes] using (theta_state_limb_value cached w holds lane ⟨limb, bound⟩).2
    _ = _ := pack_byte_pairs bytes

/-- The complete native D lane equals its eight actual queried bytes. -/
theorem theta_d_lane_bytes (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    thetaDLaneValue cached w = packByteLane (Vector.ofFn fun digit : Fin 8 => (thetaDByte cached w digit).val) := by
  let bytes := Vector.ofFn fun digit : Fin 8 => (thetaDByte cached w digit).val
  change packLane (Vector.ofFn fun limb : Fin 4 => thetaDLimbValue cached w limb) = _
  calc
    _ = packLane (Vector.ofFn fun limb : Fin 4 =>
        bytes[(⟨2 * limb.val, by omega⟩ : Fin 8)] +
          256 * bytes[(⟨2 * limb.val + 1, by omega⟩ : Fin 8)]) := by
      rfl
    _ = _ := pack_byte_pairs bytes

/-- All actual state/D byte XORs pack to the complete original input-lane XOR. -/
theorem theta_xored_lane_value (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (lane : Fin 5) :
    packByteLane (thetaXoredStateBytes cached w lane) =
      thetaLaneValue cached false w ⟨lane.val, by omega⟩ ^^^ thetaDLaneValue cached w := by
  rw [theta_state_lane_bytes cached w holds lane, theta_d_lane_bytes]
  let a := Vector.ofFn fun digit : Fin 8 => (thetaStateByte cached w lane digit).val
  let b := Vector.ofFn fun digit : Fin 8 => (thetaDByte cached w digit).val
  have aBound (digit : Fin 8) : a[digit] < 256 := by
    simpa [a] using theta_state_byte_bound cached w holds lane digit
  have bBound (digit : Fin 8) : b[digit] < 256 := by
    simpa [b] using (theta_d_operand_bounds cached w holds digit).2.2
  simpa [a, b, thetaXoredStateBytes] using pack_byte_lane_xor aBound bBound

/-- The actual written state lane packs all eight exact original rotation bytes. -/
theorem theta_write_lane_bytes (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (column lane : Fin 5)
    (flags : ∀ selected : Fin 5, thetaColumnFlag cached w selected = if selected.val = column.val then 1 else 0) :
    thetaLaneValue cached true w ⟨lane.val, by omega⟩ =
      packByteLane ((Vector.finRange 8).map
        (rotatedLaneByte (thetaXoredStateBytes cached w lane) (Call.rotations[column][lane]))) := by
  let bytes := (Vector.finRange 8).map
    (rotatedLaneByte (thetaXoredStateBytes cached w lane) (Call.rotations[column][lane]))
  calc
    _ = packLane (Vector.ofFn fun limb : Fin 4 =>
        bytes[(⟨2 * limb.val, by omega⟩ : Fin 8)] +
          256 * bytes[(⟨2 * limb.val + 1, by omega⟩ : Fin 8)]) := by
      unfold thetaLaneValue
      congr 1
      apply Vector.ext
      intro limb bound
      simpa [bytes] using theta_write_limb_rotation cached w holds column lane ⟨limb, bound⟩ flags
    _ = _ := pack_byte_pairs bytes

/-- The actual complete native state write equals the unchanged original theta/rho lane operation. -/
theorem theta_native_lane_operation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (column lane : Fin 5)
    (flags : ∀ selected : Fin 5, thetaColumnFlag cached w selected = if selected.val = column.val then 1 else 0)
    (bounds : ∀ limb : Fin 4, (thetaLaneLimb cached false w 6 limb).val < 65536) :
    thetaLaneValue cached true w ⟨lane.val, by omega⟩ =
      rotLeft64 (thetaLaneValue cached false w ⟨lane.val, by omega⟩ ^^^
        (thetaLaneValue cached false w 5 ^^^ rotLeft64 (thetaLaneValue cached false w 6) 1))
        (Call.rotations[column][lane]) := by
  rw [theta_write_lane_bytes cached w holds column lane flags,
    ← rotate_left_of_bytes (theta_xored_state_byte_bound cached w holds lane),
    theta_xored_lane_value cached w holds lane, theta_d_native_reference cached w holds bounds]
  rfl

/-- Each actual selected state write has a canonical sixty-four-bit lane value. -/
theorem theta_write_lane_bound (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (column lane : Fin 5)
    (flags : ∀ selected : Fin 5, thetaColumnFlag cached w selected = if selected.val = column.val then 1 else 0) :
    thetaLaneValue cached true w ⟨lane.val, by omega⟩ < 2 ^ 64 := by
  have h0 := (theta_write_limb_value cached w holds column lane 0 flags).1
  have h1 := (theta_write_limb_value cached w holds column lane 1 flags).1
  have h2 := (theta_write_limb_value cached w holds column lane 2 flags).1
  have h3 := (theta_write_limb_value cached w holds column lane 3 flags).1
  change (thetaLaneLimb cached true w ⟨lane.val, by omega⟩ 0).val + 65536 *
    ((thetaLaneLimb cached true w ⟨lane.val, by omega⟩ 1).val + 65536 *
      ((thetaLaneLimb cached true w ⟨lane.val, by omega⟩ 2).val + 65536 *
        (thetaLaneLimb cached true w ⟨lane.val, by omega⟩ 3).val)) < 2 ^ 64
  norm_num only [Nat.reducePow]
  omega

end Airbender.Keccak.Split.Native.Proofs
