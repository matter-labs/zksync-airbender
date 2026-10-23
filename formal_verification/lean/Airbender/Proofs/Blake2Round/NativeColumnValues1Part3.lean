import Airbender.Review.Circuits.Blake2G.Tables.Setup
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Blake2G.FrameQueryBindings
import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeColumnView1
import Airbender.Proofs.Blake2Round.NativeXorPadDefinitions

namespace Airbender.Blake2Round.Proofs.NativeColumnRows1Part3
open Blake2G.Proofs.FrameQueryShapes NativeColumnView1
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem columns9 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry9 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeColumnAssignment 1 w))) =
      combinedLowPad (source7.map (Expression.eval (Verification.environment w))) := by
  change (entry9 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (columnFrame 1 w).assignment)) = _
  rw [rawRow9, frame_eq, source7_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [values9, frame, source7Values, combinedLowPad, Arithmetic.combinedLow_as_value] <;> ring)

theorem columns10 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry10 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeColumnAssignment 1 w))) =
      carryPad 0 (source10.map (Expression.eval (Verification.environment w))) := by
  change (entry10 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (columnFrame 1 w).assignment)) = _
  rw [rawRow10, frame_eq, source10_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values10, frame, source10Values, carryPad]

theorem columns11 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry11 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeColumnAssignment 1 w))) =
      plainPad (source8.map (Expression.eval (Verification.environment w))) := by
  change (entry11 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (columnFrame 1 w).assignment)) = _
  rw [rawRow11, frame_eq, source8_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [values11, frame, source8Values, plainPad] <;> ring)

end Airbender.Blake2Round.Proofs.NativeColumnRows1Part3
