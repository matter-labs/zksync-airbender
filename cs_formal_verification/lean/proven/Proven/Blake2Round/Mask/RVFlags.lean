module
public import Proven.Blake2Round.Mask.RVControl
public import Human.ISA.BlakeRoundMask

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Every native round mask bit is the corresponding bit of the RV control word. -/
theorem native_mask_bits {w : Nat → ZMod babyBearModulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    (bounded : (inputOf w).controller.Bounded) (r : Fin 10) :
    RV.Delegation.roundMaskBit (inputOf w).controller.toBitVec r = (inputOf w).rounds r := by
  change (inputOf w).controller.toBitVec.getLsbD (19 + r.val) = decide (w (142 + r.val) = 1)
  have bit := native_control_bit holds bounded ⟨3 + r.val, by have := r.isLt; omega⟩
  simpa only [← Nat.add_assoc, Nat.reduceAdd] using bit

/-- The reduced, right-input and compression flags are the RV mode bits. -/
theorem native_mode_bits {w : Nat → ZMod babyBearModulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    (bounded : (inputOf w).controller.Bounded) :
    (inputOf w).controller.toBitVec.getLsbD 16 = (inputOf w).reducedRounds ∧
    (inputOf w).controller.toBitVec.getLsbD 17 = (inputOf w).inputIsRight ∧
    (inputOf w).controller.toBitVec.getLsbD 18 = (inputOf w).compression := by
  exact ⟨native_control_bit holds bounded 0, native_control_bit holds bounded 1,
    native_control_bit holds bounded 2⟩

/-- Native Boolean control equations exclude high RV control bits. -/
theorem native_control_lt {w : Nat → ZMod babyBearModulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    (bounded : (inputOf w).controller.Bounded) : (inputOf w).controller.toBitVec.toNat < 2 ^ 29 := by
  have mapping := native_mapping holds
  have control := Control.Proofs.soundness (by decide) setupTable
    (inputOf w).controller (outputOf w).controller w
    ⟨holds, mapping.controller.trans (control_read w), mapping.controllerOutput.trans (control_write w)⟩
  rw [Word.toBitVec_toNat bounded]
  have low := bounded.1
  change (inputOf w).controller.lo < 65536 at low
  change (inputOf w).controller.lo + 65536 * (inputOf w).controller.hi < 536870912
  have high := control.1
  omega

end Airbender.Blake2Round.Mask.Proofs
