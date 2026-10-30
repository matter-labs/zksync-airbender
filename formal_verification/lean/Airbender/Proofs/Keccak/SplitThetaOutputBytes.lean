import Airbender.Proofs.Keccak.SplitThetaOutputEquations
import Airbender.Proofs.Arithmetic.ByteLanePacking

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- The eight actual state bytes after their native D-byte XOR. -/
def thetaXoredStateBytes (cached : Bool) (w : Nat → ZMod babyBearModulus) (lane : Fin 5) : Vector Nat 8 :=
  Vector.ofFn fun digit : Fin 8 => (thetaStateByte cached w lane digit).val ^^^ (thetaDByte cached w digit).val

/-- Each complete actual state/D byte XOR remains a canonical byte. -/
theorem theta_xored_state_byte_bound (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (lane : Fin 5) (digit : Fin 8) :
    (thetaXoredStateBytes cached w lane)[digit] < 256 := by
  have bound := Nat.xor_lt_two_pow (n := 8) (theta_state_byte_bound cached w holds lane digit)
    (theta_d_operand_bounds cached w holds digit).2.2
  simpa [thetaXoredStateBytes] using bound

/-- Each actual output-byte expression has the unchanged original byte-rotation value. -/
theorem theta_output_byte_value (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (column lane : Fin 5) (digit : Fin 8)
    (flags : ∀ selected : Fin 5, thetaColumnFlag cached w selected = if selected.val = column.val then 1 else 0) :
    (thetaOutputByte cached w lane (Call.rotations[column][lane]) digit).val =
      rotatedLaneByte (thetaXoredStateBytes cached w lane) (Call.rotations[column][lane]) digit := by
  let left := Call.rotations[column][lane]
  let bytes := thetaXoredStateBytes cached w lane
  let source := byteRotationSource left digit
  let prior := byteRotationPrevious source
  have low := (theta_fragment_byte_operation cached w holds lane source).1
  have high := (theta_fragment_byte_operation cached w holds lane prior).2
  have shift := theta_rotation_shift_value cached w column lane flags
  change (thetaRotationShift cached w lane).val = left.val % 8 at shift
  rw [shift] at low high
  have lowValue : (thetaFragmentByte cached false w lane source).val =
      (bytes[source] * 2 ^ (left.val % 8)) % 256 := by
    simpa [bytes, thetaXoredStateBytes] using low
  have highValue : (thetaFragmentByte cached true w lane prior).val =
      bytes[prior] / 2 ^ (8 - left.val % 8) := by
    simpa [bytes, thetaXoredStateBytes] using high
  have priorIndex : (⟨(digit.val + 7 - left.val / 8) % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) = prior := by
    apply Fin.ext
    dsimp [prior, source, byteRotationSource, byteRotationPrevious]
    have := left.isLt
    have := digit.isLt
    omega
  have output : thetaOutputByte cached w lane left digit =
      thetaFragmentByte cached false w lane source +
        if left.val % 8 = 0 then 0 else thetaFragmentByte cached true w lane prior := by
    dsimp only [thetaOutputByte]
    rw [priorIndex]
    rfl
  change (thetaOutputByte cached w lane left digit).val = rotatedLaneByte bytes left digit
  rw [output]
  by_cases zero : left.val % 8 = 0
  · rw [if_pos zero, add_zero, lowValue]
    have priorBound : bytes[prior] < 256 := theta_xored_state_byte_bound cached w holds lane prior
    change (bytes[source] * 2 ^ (left.val % 8)) % 256 =
      (bytes[source] * 2 ^ (left.val % 8)) % 256 + bytes[prior] / 2 ^ (8 - left.val % 8)
    simp only [zero, Nat.sub_zero, Nat.reducePow, Nat.div_eq_of_lt priorBound, Nat.add_zero]
  · rw [if_neg zero]
    have lowBound := theta_fragment_byte_bound cached false w holds lane source
    have highBound := theta_fragment_byte_bound cached true w holds lane prior
    have small : (thetaFragmentByte cached false w lane source).val +
        (thetaFragmentByte cached true w lane prior).val < babyBearModulus := by
      unfold babyBearModulus; omega
    have cast : (((thetaFragmentByte cached false w lane source).val +
        (thetaFragmentByte cached true w lane prior).val : Nat) : ZMod babyBearModulus) =
        thetaFragmentByte cached false w lane source + thetaFragmentByte cached true w lane prior := by
      simp only [Nat.cast_add, ZMod.natCast_zmod_val]
    rw [← cast, ZMod.val_natCast_of_lt small, lowValue, highValue]
    rfl

/-- Exact selected native fragments give a canonical bounded output byte. -/
theorem theta_output_byte_bound (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (column lane : Fin 5) (digit : Fin 8)
    (flags : ∀ selected : Fin 5, thetaColumnFlag cached w selected = if selected.val = column.val then 1 else 0) :
    (thetaOutputByte cached w lane (Call.rotations[column][lane]) digit).val < 256 := by
  rw [theta_output_byte_value cached w holds column lane digit flags]
  exact rotated_lane_byte_bound (theta_xored_state_byte_bound cached w holds lane) _ digit

end Airbender.Keccak.Split.Native.Proofs
