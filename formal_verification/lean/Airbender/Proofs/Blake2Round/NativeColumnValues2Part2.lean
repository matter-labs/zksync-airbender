import Airbender.Review.Circuits.Blake2G.Tables.Setup
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Blake2G.FrameQueryBindings
import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeColumnView2
import Airbender.Proofs.Blake2Round.NativeXorPadDefinitions

namespace Airbender.Blake2Round.Proofs.NativeColumnRows2Part2
open Blake2G.Proofs.FrameQueryShapes NativeColumnView2
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem columns6 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry6 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeColumnAssignment 2 w))) =
      combinedLowPad (source6.map (Expression.eval (Verification.environment w))) := by
  change (entry6 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (columnFrame 2 w).assignment)) = _
  rw [rawRow6, frame_eq, source6_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [values6, frame, source6Values, combinedLowPad, Arithmetic.combinedLow_as_value] <;> ring)

theorem columns7 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry7 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeColumnAssignment 2 w))) =
      combinedHighPad (source6.map (Expression.eval (Verification.environment w))) := by
  change (entry7 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (columnFrame 2 w).assignment)) = _
  rw [rawRow7, frame_eq, source6_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values7, frame, source6Values, combinedHighPad]

theorem columns8 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry8 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeColumnAssignment 2 w))) =
      plainPad (source5.map (Expression.eval (Verification.environment w))) := by
  change (entry8 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (columnFrame 2 w).assignment)) = _
  rw [rawRow8, frame_eq, source5_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values8, frame, source5Values, plainPad]

end Airbender.Blake2Round.Proofs.NativeColumnRows2Part2
