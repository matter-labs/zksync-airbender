import Airbender.Proofs.Keccak.SplitThetaBytes
import Airbender.Proofs.Arithmetic.ByteAssembly
import Mathlib.Tactic.ReduceModChar

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- Every actual native state read limb equals its two queried byte operands. -/
theorem theta_state_limb_packing (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 5) (limb : Fin 4) :
    thetaLaneLimb cached false w ⟨lane.val, by omega⟩ limb =
      thetaStateByte cached w lane ⟨2 * limb.val, by omega⟩ +
        256 * thetaStateByte cached w lane ⟨2 * limb.val + 1, by omega⟩ := by
  cases cached <;> fin_cases lane <;> fin_cases limb <;>
    dsimp only [thetaLaneLimb, thetaStateByte, Row.ports, WordColumns.evaluate,
      ThetaRho.importedConstraintsMemoryPorts, ThetaRhoCached.importedConstraintsMemoryPorts,
      thetaRhoQueryEntry, thetaRhoQuery, ThetaRho.importedConstraints,
      ThetaRhoCached.importedConstraints, FlatOperation.lookups, List.get, Expression.eval,
      Verification.environment] <;>
    norm_num [Fin.getElem_fin, Expression.eval, Verification.environment] <;> ring_nf <;>
    unfold babyBearModulus at * <;> reduce_mod_char <;> ring_nf <;> reduce_mod_char

/-- Every actual native previous-column read limb equals its two queried byte operands. -/
theorem theta_previous_limb_packing (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (limb : Fin 4) :
    thetaLaneLimb cached false w 5 limb =
      thetaPreviousByte cached w ⟨2 * limb.val, by omega⟩ +
        256 * thetaPreviousByte cached w ⟨2 * limb.val + 1, by omega⟩ := by
  cases cached <;> fin_cases limb <;>
    dsimp only [thetaLaneLimb, thetaPreviousByte, Row.ports, WordColumns.evaluate,
      ThetaRho.importedConstraintsMemoryPorts, ThetaRhoCached.importedConstraintsMemoryPorts,
      thetaRhoQueryEntry, thetaRhoQuery, ThetaRho.importedConstraints,
      ThetaRhoCached.importedConstraints, FlatOperation.lookups, List.get, Expression.eval,
      Verification.environment] <;>
    norm_num [Fin.getElem_fin, Expression.eval, Verification.environment] <;> ring_nf <;>
    unfold babyBearModulus at * <;> reduce_mod_char <;> ring_nf <;> reduce_mod_char

/-- All actual state read limbs have their canonical bounded byte expansion. -/
theorem theta_state_limb_value (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (lane : Fin 5) (limb : Fin 4) :
    (thetaLaneLimb cached false w ⟨lane.val, by omega⟩ limb).val < 65536 ∧
      (thetaLaneLimb cached false w ⟨lane.val, by omega⟩ limb).val =
        (thetaStateByte cached w lane ⟨2 * limb.val, by omega⟩).val +
          256 * (thetaStateByte cached w lane ⟨2 * limb.val + 1, by omega⟩).val := by
  have low := theta_state_byte_bound cached w holds lane ⟨2 * limb.val, by omega⟩
  have high := theta_state_byte_bound cached w holds lane ⟨2 * limb.val + 1, by omega⟩
  have value := value_of_bounded_pair (radix := 256) (capacity := 256) (by decide) low high
    (theta_state_limb_packing cached w lane limb).symm
  exact ⟨by rw [value]; omega, value⟩

/-- Every actual previous-column read limb has its canonical bounded byte expansion. -/
theorem theta_previous_limb_value (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (limb : Fin 4) :
    (thetaLaneLimb cached false w 5 limb).val < 65536 ∧
      (thetaLaneLimb cached false w 5 limb).val =
        (thetaPreviousByte cached w ⟨2 * limb.val, by omega⟩).val +
          256 * (thetaPreviousByte cached w ⟨2 * limb.val + 1, by omega⟩).val := by
  have low := (theta_d_operand_bounds cached w holds ⟨2 * limb.val, by omega⟩).1
  have high := (theta_d_operand_bounds cached w holds ⟨2 * limb.val + 1, by omega⟩).1
  have value := value_of_bounded_pair (radix := 256) (capacity := 256) (by decide) low high
    (theta_previous_limb_packing cached w limb).symm
  exact ⟨by rw [value]; omega, value⟩

end Airbender.Keccak.Split.Native.Proofs
