import Airbender.Review.Circuits.Blake2G.Tables.Setup
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2G.FrameQueryBindings
import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeDiagonalView3
import Airbender.Proofs.Blake2Round.NativeXorPadDefinitions
import Mathlib.Tactic.LinearCombination

namespace Airbender.Blake2Round.Proofs.NativeDiagonalRows3Part5
open Blake2G.Proofs.FrameQueryShapes NativeDiagonalView3
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem columns15 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry15 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 3 w))) =
      plainPad (source12.map (Expression.eval (Verification.environment w))) := by
  change (entry15 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 3 w).assignment)) = _
  rw [rawRow15, frame_eq, source12_eval]
  have characteristic : (2013265921 : ZMod p) = 0 := by
    linear_combination -compatible
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [values15, frame, source12Values, plainPad] <;> first
    | linear_combination (0) * characteristic
    | linear_combination (512 * w 308 + 512 * w 329 + 2 * w 513) * characteristic
)

theorem columns16 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry16 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 3 w))) =
      carryPad 1 (source15.map (Expression.eval (Verification.environment w))) := by
  change (entry16 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 3 w).assignment)) = _
  rw [rawRow16, frame_eq, source15_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values16, frame, source15Values, carryPad]

theorem columns17 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry17 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 3 w))) =
      plainPad (source13.map (Expression.eval (Verification.environment w))) := by
  change (entry17 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 3 w).assignment)) = _
  rw [rawRow17, frame_eq, source13_eval]
  have characteristic : (2013265921 : ZMod p) = 0 := by
    linear_combination -compatible
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [values17, frame, source13Values, plainPad] <;> first
    | linear_combination (0) * characteristic
    | linear_combination (512 * w 311 + 512 * w 331 + 2 * w 511 + 61440 * w 305 + 61440 * w 327 + 61440 * w 513) * characteristic
)

end Airbender.Blake2Round.Proofs.NativeDiagonalRows3Part5
