import Slop.UnifiedReduced.ControlResolution
import Human.Circuits.JumpBranchSlt.Artifact

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Verification
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def controlAssignment (w : Nat → ZMod p) (i : Nat) : ZMod p :=
  match i with
  | 2 | 3 | 19 | 49 | 50 | 51 => 0
  | 18 => 4
  | 11 => w 21 | 12 => w 22 | 13 => w 23 | 14 => w 24 | 15 => w 25
  | 16 => w 30 | 17 => w 31
  | 22 => w 36 | 23 => w 37 | 26 => w 42 | 27 => w 43
  | 30 => w 50 | 31 => w 51
  | 34 => w 78 | 35 => w 79 | 36 => w 81
  | 37 => w 52 | 38 => w 53 | 39 => w 54 | 40 => w 55
  | 41 => w 57 | 42 => w 58 | 43 => w 60 | 44 => w 59 | 45 => w 82 | 46 => w 56
  | 47 => w 23 * w 59 + (w 21 + w 22) * w 78
  | 48 => (w 21 + w 22) * w 79
  | i => w i

theorem control_assertions [Fact p.Prime] {setup : Table (ZMod p) (fields 10)}
    {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (jumps : w 21 = 0 ∧ w 22 = 0) (selected : w 23 + w 24 = 1)
    (discarded : w 24 * (1 - w 25) = 0) :
    ∀ i : Fin 26, ((FlatOperation.constraints (JumpBranchSlt.importedConstraints (p := p))).get i).eval
      (Verification.environment (controlAssignment w)) = 0 := by
  have equation (i : Fin 27) := Verification.assertion_of_holds holds
    ⟨i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  have e0 := equation 0; have e12 := equation 12; have e13 := equation 13
  have e14 := equation 14; have e15 := equation 15; have e16 := equation 16; have e17 := equation 17
  have e18 := equation 18; have e19 := equation 19; have e20 := equation 20; have e21 := equation 21
  have e22 := equation 22; have e23 := equation 23
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, jumps.1, jumps.2, selected] at e0 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23
  have maskedLow : w 85 * w 50 = 0 := by
    simpa [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment] using equation 25
  have comparedHigh : w 84 * w 51 = 0 := by
    simpa [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment] using equation 24
  have maskedHigh : w 85 * w 51 = 0 := by
    simpa [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment] using equation 26
  have writer : w 83 = 0 := by
    linear_combination e19
  have mask : w 85 = w 25 := by
    linear_combination e21
  have compare : w 84 = w 23 * (1 - w 25) := by linear_combination e20
  have partition : w 84 + w 85 = 1 := by
    rw [compare, mask]
    linear_combination (1 - w 25) * selected - discarded
  have low : (1 - w 25) * (w 23 * w 59) - w 50 = 0 := by
    rw [writer] at e22
    linear_combination e22 - maskedLow - w 59 * compare + w 50 * partition
  have high : w 51 = 0 := by
    linear_combination comparedHigh + maskedHigh - w 51 * partition
  intro i
  fin_cases i
  all_goals simp [JumpBranchSlt.importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, controlAssignment, jumps.1, jumps.2]
  all_goals solve
    | exact e0
    | linear_combination e12
    | linear_combination e13
    | linear_combination e14
    | linear_combination e15
    | linear_combination e16
    | linear_combination e17
    | exact e18
    | linear_combination low
    | exact high
    | (have flag := local_flags holds 13; change w 23 = 0 ∨ w 23 = 1 at flag; rcases flag with bit | bit <;> simp [bit])
    | (have flag := local_flags holds 14; change w 24 = 0 ∨ w 24 = 1 at flag; rcases flag with bit | bit <;> simp [bit])
    | (have flag := local_flags holds 15; change w 25 = 0 ∨ w 25 = 1 at flag; rcases flag with bit | bit <;> simp [bit])
    | (have flag := local_flags holds 20; change w 52 = 0 ∨ w 52 = 1 at flag; rcases flag with bit | bit <;> simp [bit])
    | (have flag := local_flags holds 21; change w 53 = 0 ∨ w 53 = 1 at flag; rcases flag with bit | bit <;> simp [bit])
    | (have flag := local_flags holds 22; change w 54 = 0 ∨ w 54 = 1 at flag; rcases flag with bit | bit <;> simp [bit])
    | (have flag := local_flags holds 23; change w 55 = 0 ∨ w 55 = 1 at flag; rcases flag with bit | bit <;> simp [bit])

end Airbender.UnifiedReduced.Proofs
