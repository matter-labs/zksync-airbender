import Airbender.Review.Circuits.Blake2G.Tables.Setup
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2G.FrameQueryBindings
import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeDiagonalView3
import Airbender.Proofs.Blake2Round.NativeXorPadDefinitions
import Mathlib.Tactic.LinearCombination

namespace Airbender.Blake2Round.Proofs.NativeDiagonalRows3Part2
open Blake2G.Proofs.FrameQueryShapes NativeDiagonalView3
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem columns6 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry6 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 3 w))) =
      combinedLowPad (source6.map (Expression.eval (Verification.environment w))) := by
  change (entry6 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 3 w).assignment)) = _
  rw [rawRow6, frame_eq, source6_eval]
  have characteristic : (2013265921 : ZMod p) = 0 := by
    linear_combination -compatible
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [values6, frame, source6Values, combinedLowPad, Arithmetic.combinedLow_as_value] <;> first
    | linear_combination (0) * characteristic
    | linear_combination (16 * w 308 + 16 * w 329) * characteristic
)

theorem columns7 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry7 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 3 w))) =
      combinedHighPad (source6.map (Expression.eval (Verification.environment w))) := by
  change (entry7 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 3 w).assignment)) = _
  rw [rawRow7, frame_eq, source6_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values7, frame, source6Values, combinedHighPad]

theorem columns8 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry8 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 3 w))) =
      plainPad (source5.map (Expression.eval (Verification.environment w))) := by
  change (entry8 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 3 w).assignment)) = _
  rw [rawRow8, frame_eq, source5_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values8, frame, source5Values, plainPad]

end Airbender.Blake2Round.Proofs.NativeDiagonalRows3Part2
