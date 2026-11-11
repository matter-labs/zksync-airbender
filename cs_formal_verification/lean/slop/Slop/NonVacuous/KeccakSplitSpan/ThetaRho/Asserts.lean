module
public import Slop.NonVacuous.KeccakSplitSpan.ThetaRho.RotationB

@[expose] public section

/-! The 35 imported assertions of a theta+rho row hold for the honest assignment of valid inputs: the active flag,
    the zero high limbs of x10, the twenty rotation equations (each written limb is the bytes its fragments place,
    under the one-hot column flags), the four grouped read clocks at their schedule distances, and the four top
    bits of `C[x+1]`. -/

namespace Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
open Arithmetic Keccak.Split Keccak.Split.SetupProofs

/-- The grouped read clocks of a theta+rho call: x10 and x11 last written by the previous call, the five lanes by
    the column-parity call five before, `C[x-1]` and `C[x+1]` at their column's distances. -/
structure Clocks (x : RowInput) : Prop where
  registers : x.previous 0 + 4 = x.invocation + 2
  lanes : x.previous 2 + 20 = x.invocation + 2
  before : x.previous 12 + 4 * (flag x 0 + 6 * flag x 1 + 2 * flag x 2 + 2 * flag x 3 + 2 * flag x 4) =
    x.invocation + 2
  after : x.previous 14 + 4 * (4 * flag x 0 + 4 * flag x 1 + 4 * flag x 2 + 3 * flag x 3 + 3 * flag x 4) =
    x.invocation + 2

variable {p : Nat} [Fact p.Prime]

theorem asserts (x : RowInput) (valid : x.Valid) (kind : kindAt x.call = .thetaRho) (clocks : Clocks x)
    (setup : Table (ZMod p) (fields 9)) :
    ∀ i (h : i < (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length),
      ((FlatOperation.constraints (ThetaRho.importedConstraints setup)).get ⟨i, h⟩).eval
        (Verification.environment (assignment x)) = 0 := by
  have top (m : Nat) : top x m ≤ 1 := by
    have := valid.limb (l := 6) (by rw [kind]; decide) m
    unfold top
    omega
  intro i h
  have size : i < 35 := by
    have count : (FlatOperation.constraints (ThetaRho.importedConstraints setup)).length = 35 := by rfl
    omega
  interval_cases i <;> op_index
  · simp only [Expression.eval, Verification.environment, honest_column]
    push_cast
    ring
  · simp only [Expression.eval, Verification.environment, honest_column, Nat.cast_zero]
  · simp only [Expression.eval, Verification.environment, honest_column, Nat.cast_zero]
  · exact rotation_3 x setup
  · exact rotation_4 x setup
  · exact rotation_5 x setup
  · exact rotation_6 x setup
  · exact rotation_7 x setup
  · exact rotation_8 x setup
  · exact rotation_9 x setup
  · exact rotation_10 x setup
  · exact rotation_11 x setup
  · exact rotation_12 x setup
  · exact rotation_13 x setup
  · exact rotation_14 x setup
  · exact rotation_15 x setup
  · exact rotation_16 x setup
  · exact rotation_17 x setup
  · exact rotation_18 x setup
  · exact rotation_19 x setup
  · exact rotation_20 x setup
  · exact rotation_21 x setup
  · exact rotation_22 x setup
  · cast_identity p clocks.registers
  · simp only [Expression.eval, Verification.environment, honest_column]
    ring
  · cast_identity p clocks.lanes
  · simp only [Expression.eval, Verification.environment, honest_column]
    ring
  · cast_identity p clocks.before
  · simp only [Expression.eval, Verification.environment, honest_column]
    ring
  · cast_identity p clocks.after
  · simp only [Expression.eval, Verification.environment, honest_column]
    ring
  · exact flag_eval (assignment_68 x) (top 0)
  · exact flag_eval (assignment_69 x) (top 1)
  · exact flag_eval (assignment_70 x) (top 2)
  · exact flag_eval (assignment_71 x) (top 3)

end Airbender.NonVacuous.KeccakSplitSpan.ThetaRho
