import Airbender.Proofs.Keccak.SplitThetaNextRotation

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- Two actual native D bytes form one complete canonical limb. -/
def thetaDLimbValue (cached : Bool) (w : Nat → ZMod babyBearModulus) (limb : Fin 4) : Nat :=
  (thetaDByte cached w ⟨2 * limb.val, by omega⟩).val +
    256 * (thetaDByte cached w ⟨2 * limb.val + 1, by omega⟩).val

/-- The actual native D limb is XOR of the corresponding complete parity operands. -/
theorem theta_d_limb_operation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (limb : Fin 4) :
    thetaDLimbValue cached w limb =
      (thetaLaneLimb cached false w 5 limb).val ^^^ thetaRotatedLimbValue cached w limb := by
  have previous := (theta_previous_limb_value cached w holds limb).2
  have low := theta_d_operand_bounds cached w holds ⟨2 * limb.val, by omega⟩
  have chunks := xor_of_chunks (width := 8) low.1 low.2.1
    (a₁ := (thetaPreviousByte cached w ⟨2 * limb.val + 1, by omega⟩).val)
    (b₁ := (thetaRotatedByte cached w ⟨2 * limb.val + 1, by omega⟩).val)
  norm_num only [Nat.reducePow] at chunks
  rw [previous]
  unfold thetaRotatedLimbValue thetaDLimbValue
  rw [theta_d_byte_operation cached w holds ⟨2 * limb.val, by omega⟩,
    theta_d_byte_operation cached w holds ⟨2 * limb.val + 1, by omega⟩]
  exact chunks.symm

/-- The actual complete native D lane. -/
def thetaDLaneValue (cached : Bool) (w : Nat → ZMod babyBearModulus) : Nat :=
  packLane (Vector.ofFn fun limb : Fin 4 => thetaDLimbValue cached w limb)

/-- The actual complete previous-parity memory lane. -/
def thetaPreviousLaneValue (cached : Bool) (w : Nat → ZMod babyBearModulus) : Nat :=
  packLane (Vector.ofFn fun limb : Fin 4 => (thetaLaneLimb cached false w 5 limb).val)

/-- All actual D bytes combine to the complete native lane XOR. -/
theorem theta_d_lane_operation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) :
    thetaDLaneValue cached w = thetaPreviousLaneValue cached w ^^^ thetaRotatedLaneValue cached w := by
  have a (limb : Fin 4) := (theta_previous_limb_value cached w holds limb).1
  have b (limb : Fin 4) := theta_rotated_limb_bound cached w holds limb
  have chunks := xor_of_four_chunks (width := 16) (a 0) (a 1) (a 2) (b 0) (b 1) (b 2)
    (a₃ := (thetaLaneLimb cached false w 5 3).val) (b₃ := thetaRotatedLimbValue cached w 3)
  norm_num only [Nat.reducePow] at chunks
  unfold thetaDLaneValue thetaPreviousLaneValue thetaRotatedLaneValue packLane
  simp only [Vector.getElem_ofFn, theta_d_limb_operation cached w holds]
  exact chunks.symm

/-- Initialized next-parity reads give the unchanged original complete D-lane relation. -/
theorem theta_d_native_reference (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable))
    (bounds : ∀ limb : Fin 4, (thetaLaneLimb cached false w 6 limb).val < 65536) :
    thetaDLaneValue cached w =
      thetaPreviousLaneValue cached w ^^^ rotLeft64 (thetaNextLaneValue cached w) 1 := by
  rw [theta_d_lane_operation cached w holds, theta_native_next_rotation cached w holds bounds]

end Airbender.Keccak.Split.Native.Proofs
