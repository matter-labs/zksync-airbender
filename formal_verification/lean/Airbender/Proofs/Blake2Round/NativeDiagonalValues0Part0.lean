import Airbender.Review.Circuits.Blake2G.Tables.Setup
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2G.FrameQueryBindings
import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeDiagonalView0
import Airbender.Proofs.Blake2Round.NativeXorPadDefinitions
import Mathlib.Tactic.LinearCombination

namespace Airbender.Blake2Round.Proofs.NativeDiagonalRows0Part0
open Blake2G.Proofs.FrameQueryShapes NativeDiagonalView0
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem columns0 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry0 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 0 w))) =
      carryPad 0 (source0.map (Expression.eval (Verification.environment w))) := by
  change (entry0 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 0 w).assignment)) = _
  rw [rawRow0, frame_eq, source0_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values0, frame, source0Values, carryPad]

theorem columns1 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry1 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 0 w))) =
      plainPad (source1.map (Expression.eval (Verification.environment w))) := by
  change (entry1 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 0 w).assignment)) = _
  rw [rawRow1, frame_eq, source1_eval]
  have characteristic : (2013265921 : ZMod p) = 0 := by
    linear_combination -compatible
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [values1, frame, source1Values, plainPad] <;> first
    | linear_combination (-w 407) * characteristic
    | linear_combination (256 * w 257 + 256 * w 281 - 2 * w 335) * characteristic
)

theorem columns2 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry2 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 0 w))) =
      carryPad 0 (source2.map (Expression.eval (Verification.environment w))) := by
  change (entry2 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 0 w).assignment)) = _
  rw [rawRow2, frame_eq, source2_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values2, frame, source2Values, carryPad]

end Airbender.Blake2Round.Proofs.NativeDiagonalRows0Part0
