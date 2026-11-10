import Airbender.Review.Circuits.Blake2G.Tables.Setup
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2G.FrameQueryBindings
import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeDiagonalView1
import Airbender.Proofs.Blake2Round.NativeXorPadDefinitions
import Mathlib.Tactic.LinearCombination

namespace Airbender.Blake2Round.Proofs.NativeDiagonalRows1Part4
open Blake2G.Proofs.FrameQueryShapes NativeDiagonalView1
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem columns12 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry12 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 1 w))) =
      carryPad 0 (source11.map (Expression.eval (Verification.environment w))) := by
  change (entry12 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 1 w).assignment)) = _
  rw [rawRow12, frame_eq, source11_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values12, frame, source11Values, carryPad]

theorem columns13 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry13 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 1 w))) =
      plainPad (source9.map (Expression.eval (Verification.environment w))) := by
  change (entry13 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 1 w).assignment)) = _
  rw [rawRow13, frame_eq, source9_eval]
  have characteristic : (2013265921 : ZMod p) = 0 := by
    linear_combination -compatible
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [values13, frame, source9Values, plainPad] <;> first
    | linear_combination (0) * characteristic
    | linear_combination (256 * w 299 + 256 * w 323 + 15360 * w 317 + 61440 * w 375 + 15360 * w 465) * characteristic
)

theorem columns14 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry14 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeDiagonalAssignment 1 w))) =
      carryPad 1 (source14.map (Expression.eval (Verification.environment w))) := by
  change (entry14 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (diagonalFrame 1 w).assignment)) = _
  rw [rawRow14, frame_eq, source14_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values14, frame, source14Values, carryPad]

end Airbender.Blake2Round.Proofs.NativeDiagonalRows1Part4
