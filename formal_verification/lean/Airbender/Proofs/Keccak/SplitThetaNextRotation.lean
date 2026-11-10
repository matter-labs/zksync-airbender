import Airbender.Proofs.Keccak.SplitThetaInputPacking
import Airbender.Proofs.Arithmetic.LaneRotation

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The four actual native top-bit variables use their original imported indices. -/
def thetaNextTop (w : Nat → ZMod babyBearModulus) (limb : Fin 4) : ZMod babyBearModulus :=
  w (68 + limb.val)

variable [Fact babyBearModulus.Prime]

/-- Each actual native next-parity top column is Boolean in both cache modes. -/
theorem theta_next_top_bit (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (limb : Fin 4) :
    thetaNextTop w limb = 0 ∨ thetaNextTop w limb = 1 := by
  cases cached
  all_goals
    have core := Verification.holds_of_sublist holds (List.sublist_append_left _ _)
    have equation := Verification.assertion_of_holds core ⟨31 + limb.val, by change 31 + limb.val < 35; omega⟩
    have polynomial : thetaNextTop w limb * (thetaNextTop w limb - 1) = 0 := by
      fin_cases limb
      all_goals
        dsimp only [ThetaRho.importedConstraints, ThetaRhoCached.importedConstraints,
          FlatOperation.constraints, List.get, Expression.eval, Verification.environment] at equation
        simpa [thetaNextTop, sub_eq_add_neg] using equation
    rcases mul_eq_zero.mp polynomial with zero | one
    · exact Or.inl zero
    · exact Or.inr (sub_eq_zero.mp one)

/-- The actual native Boolean columns have canonical zero-or-one values. -/
theorem theta_next_top_bound (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (limb : Fin 4) :
    (thetaNextTop w limb).val < 2 := by
  rcases theta_next_top_bit cached w holds limb with zero | one
  · simp [zero]
  · have valOne : (1 : ZMod babyBearModulus).val = 1 := by rfl
    rw [one, valOne]
    decide

/-- The actual byte-query expressions retain the complete native cyclic carry equation. -/
theorem theta_next_rotation_equation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (limb : Fin 4) :
    2 * thetaLaneLimb cached false w 6 limb + thetaNextTop w (rotationPrevious limb) =
      thetaRotatedByte cached w ⟨2 * limb.val, by omega⟩ +
        256 * thetaRotatedByte cached w ⟨2 * limb.val + 1, by omega⟩ +
        65536 * thetaNextTop w limb := by
  cases cached <;> fin_cases limb <;>
    dsimp only [thetaLaneLimb, thetaRotatedByte, thetaNextTop, rotationPrevious,
      Row.ports, WordColumns.evaluate, ThetaRho.importedConstraintsMemoryPorts,
      ThetaRhoCached.importedConstraintsMemoryPorts, thetaRhoQueryEntry, thetaRhoQuery,
      ThetaRho.importedConstraints, ThetaRhoCached.importedConstraints,
      FlatOperation.lookups, List.get, Expression.eval, Verification.environment] <;>
    norm_num [Fin.getElem_fin, Expression.eval, Verification.environment] <;> ring_nf <;>
    unfold babyBearModulus at * <;> reduce_mod_char <;> ring_nf <;> reduce_mod_char

/-- The actual two rotated byte values form the canonical native sixteen-bit result. -/
def thetaRotatedLimbValue (cached : Bool) (w : Nat → ZMod babyBearModulus) (limb : Fin 4) : Nat :=
  (thetaRotatedByte cached w ⟨2 * limb.val, by omega⟩).val +
    256 * (thetaRotatedByte cached w ⟨2 * limb.val + 1, by omega⟩).val

/-- Native byte membership bounds the complete rotated limb. -/
theorem theta_rotated_limb_bound (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (limb : Fin 4) :
    thetaRotatedLimbValue cached w limb < 65536 := by
  have low := (theta_d_operand_bounds cached w holds ⟨2 * limb.val, by omega⟩).2.1
  have high := (theta_d_operand_bounds cached w holds ⟨2 * limb.val + 1, by omega⟩).2.1
  unfold thetaRotatedLimbValue
  omega

/-- Initialized read bounds turn the actual native field equation into its complete integer carry equation. -/
theorem theta_next_rotation_integer (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable))
    (bounds : ∀ limb : Fin 4, (thetaLaneLimb cached false w 6 limb).val < 65536) (limb : Fin 4) :
    2 * (thetaLaneLimb cached false w 6 limb).val + (thetaNextTop w (rotationPrevious limb)).val =
      thetaRotatedLimbValue cached w limb + 65536 * (thetaNextTop w limb).val := by
  have low := (theta_d_operand_bounds cached w holds ⟨2 * limb.val, by omega⟩).2.1
  have high := (theta_d_operand_bounds cached w holds ⟨2 * limb.val + 1, by omega⟩).2.1
  have carry := theta_next_top_bound cached w holds (rotationPrevious limb)
  have top := theta_next_top_bound cached w holds limb
  have input := bounds limb
  have leftBound : 2 * (thetaLaneLimb cached false w 6 limb).val +
      (thetaNextTop w (rotationPrevious limb)).val < babyBearModulus := by
    unfold babyBearModulus; omega
  have rightBound : thetaRotatedLimbValue cached w limb +
      65536 * (thetaNextTop w limb).val < babyBearModulus := by
    unfold thetaRotatedLimbValue babyBearModulus; omega
  have field :
      ((2 * (thetaLaneLimb cached false w 6 limb).val +
        (thetaNextTop w (rotationPrevious limb)).val : Nat) : ZMod babyBearModulus) =
      ((thetaRotatedLimbValue cached w limb +
        65536 * (thetaNextTop w limb).val : Nat) : ZMod babyBearModulus) := by
    simpa only [thetaRotatedLimbValue, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      ZMod.natCast_zmod_val] using theta_next_rotation_equation cached w limb
  have equality := congrArg ZMod.val field
  simpa only [ZMod.val_natCast_of_lt leftBound, ZMod.val_natCast_of_lt rightBound] using equality

/-- Initialized read bounds force each actual native top bit to equal the input's true top bit. -/
theorem theta_next_top_value (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable))
    (bounds : ∀ limb : Fin 4, (thetaLaneLimb cached false w 6 limb).val < 65536) (limb : Fin 4) :
    (thetaNextTop w limb).val = (thetaLaneLimb cached false w 6 limb).val / 32768 := by
  have equation := theta_next_rotation_integer cached w holds bounds limb
  have carry := theta_next_top_bound cached w holds (rotationPrevious limb)
  have top := theta_next_top_bound cached w holds limb
  have rotated := theta_rotated_limb_bound cached w holds limb
  have input := bounds limb
  omega

/-- The actual native rotated limb has its exact original cyclic one-bit rotation value. -/
theorem theta_rotated_limb_value (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable))
    (bounds : ∀ limb : Fin 4, (thetaLaneLimb cached false w 6 limb).val < 65536) (limb : Fin 4) :
    thetaRotatedLimbValue cached w limb =
      (2 * (thetaLaneLimb cached false w 6 limb).val) % 65536 +
        (thetaLaneLimb cached false w 6 (rotationPrevious limb)).val / 32768 := by
  have equation := theta_next_rotation_integer cached w holds bounds limb
  rw [theta_next_top_value cached w holds bounds limb,
    theta_next_top_value cached w holds bounds (rotationPrevious limb)] at equation
  have input := bounds limb
  omega

/-- The complete actual next-parity memory lane. -/
def thetaNextLaneValue (cached : Bool) (w : Nat → ZMod babyBearModulus) : Nat :=
  packLane (Vector.ofFn fun limb : Fin 4 => (thetaLaneLimb cached false w 6 limb).val)

/-- The complete actual lane formed by the queried rotated next-parity bytes. -/
def thetaRotatedLaneValue (cached : Bool) (w : Nat → ZMod babyBearModulus) : Nat :=
  packLane (Vector.ofFn fun limb : Fin 4 => thetaRotatedLimbValue cached w limb)

/-- Initialized read bounds prove the original complete sixty-four-bit next-parity rotation. -/
theorem theta_native_next_rotation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable))
    (bounds : ∀ limb : Fin 4, (thetaLaneLimb cached false w 6 limb).val < 65536) :
    thetaRotatedLaneValue cached w = rotLeft64 (thetaNextLaneValue cached w) 1 := by
  let inputs : Vector Nat 4 := Vector.ofFn fun limb : Fin 4 =>
    (thetaLaneLimb cached false w 6 limb).val
  have small (limb : Fin 4) : inputs[limb] < 65536 := by
    simpa [inputs] using bounds limb
  have rotation := rotate_left_of_limbs small (1 : Fin 64)
  have equal : Vector.ofFn (thetaRotatedLimbValue cached w) =
      (Vector.finRange 4).map (rotatedLaneLimb inputs 1) := by
    apply Vector.ext
    intro index bound
    have value := theta_rotated_limb_value cached w holds bounds ⟨index, bound⟩
    interval_cases index
    all_goals simpa [inputs, rotatedLaneLimb, rotationSource, rotationPrevious, Nat.mul_comm] using value
  change packLane (Vector.ofFn (thetaRotatedLimbValue cached w)) = rotLeft64 (packLane inputs) 1
  rw [equal]
  exact rotation.symm

end Airbender.Keccak.Split.Native.Proofs
