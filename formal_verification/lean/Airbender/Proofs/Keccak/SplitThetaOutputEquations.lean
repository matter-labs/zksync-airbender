import Airbender.Proofs.Keccak.SplitThetaControllerQuery
import Mathlib.Tactic.LinearCombination

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- The actual fragments selected for one byte of the original rho rotation. -/
def thetaOutputByte (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 5) (left : Fin 64) (digit : Fin 8) : ZMod babyBearModulus :=
  thetaFragmentByte cached false w lane
    ⟨(digit.val + 8 - left.val / 8) % 8, Nat.mod_lt _ (by decide)⟩ +
  if left.val % 8 = 0 then 0 else thetaFragmentByte cached true w lane
    ⟨(digit.val + 7 - left.val / 8) % 8, Nat.mod_lt _ (by decide)⟩

/-- The actual low and high output bytes for one selected original rho column. -/
def thetaOutputLimbExpression (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (column lane : Fin 5) (limb : Fin 4) : ZMod babyBearModulus :=
  thetaOutputByte cached w lane (Call.rotations[column][lane]) ⟨2 * limb.val, by omega⟩ +
    256 * thetaOutputByte cached w lane (Call.rotations[column][lane]) ⟨2 * limb.val + 1, by omega⟩

/-- Native constraints bind each actual written limb to all five flag-weighted rho expressions. -/
theorem theta_native_output_equation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (lane : Fin 5) (limb : Fin 4) :
    thetaLaneLimb cached true w ⟨lane.val, by omega⟩ limb =
      thetaColumnFlag cached w 0 * thetaOutputLimbExpression cached w 0 lane limb +
      thetaColumnFlag cached w 1 * thetaOutputLimbExpression cached w 1 lane limb +
      thetaColumnFlag cached w 2 * thetaOutputLimbExpression cached w 2 lane limb +
      thetaColumnFlag cached w 3 * thetaOutputLimbExpression cached w 3 lane limb +
      thetaColumnFlag cached w 4 * thetaOutputLimbExpression cached w 4 lane limb := by
  cases cached
  all_goals
    have core := Verification.holds_of_sublist holds (List.sublist_append_left _ _)
    have equation := Verification.assertion_of_holds core
      ⟨3 + 4 * lane.val + limb.val, by change 3 + 4 * lane.val + limb.val < 35; omega⟩
    fin_cases lane <;> fin_cases limb
  all_goals
    norm_num [thetaOutputLimbExpression, thetaOutputByte, Call.rotations]
    dsimp only [ThetaRho.importedConstraints, ThetaRhoCached.importedConstraints,
      FlatOperation.constraints, List.get, Expression.eval, Verification.environment] at equation
    dsimp only [thetaLaneLimb, thetaColumnFlag, thetaQueryRow, thetaOutputLimbExpression,
      thetaOutputByte, thetaFragmentByte, thetaRhoQueryEntry, thetaRhoQuery,
      Row.ports, WordColumns.evaluate, ThetaRho.importedConstraintsMemoryPorts,
      ThetaRhoCached.importedConstraintsMemoryPorts, ThetaRho.importedConstraints,
      ThetaRhoCached.importedConstraints, FlatOperation.lookups, List.get,
      Expression.eval, Verification.environment]
    norm_num [Fin.getElem_fin, Expression.eval, Verification.environment, Call.rotations] at equation ⊢
    linear_combination -equation

/-- Exact native column flags select the complete written limb's original rho expression. -/
theorem theta_native_selected_output (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (column lane : Fin 5) (limb : Fin 4)
    (flags : ∀ selected : Fin 5, thetaColumnFlag cached w selected = if selected.val = column.val then 1 else 0) :
    thetaLaneLimb cached true w ⟨lane.val, by omega⟩ limb = thetaOutputLimbExpression cached w column lane limb := by
  rw [theta_native_output_equation cached w holds lane limb]
  fin_cases column <;> simp [flags]

end Airbender.Keccak.Split.Native.Proofs
