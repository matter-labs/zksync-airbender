import Airbender.Review.Circuits.Blake2G.Tables.Setup
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Blake2G.FrameQueryBindings
import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeColumnView1
import Airbender.Proofs.Blake2Round.NativeXorPadDefinitions

namespace Airbender.Blake2Round.Proofs.NativeColumnRows1Part1
open Blake2G.Proofs.FrameQueryShapes NativeColumnView1
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem columns3 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry3 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeColumnAssignment 1 w))) =
      plainPad (source3.map (Expression.eval (Verification.environment w))) := by
  change (entry3 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (columnFrame 1 w).assignment)) = _
  rw [rawRow3, frame_eq, source3_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [values3, frame, source3Values, plainPad] <;> ring)

theorem columns4 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry4 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeColumnAssignment 1 w))) =
      combinedHighPad (source7.map (Expression.eval (Verification.environment w))) := by
  change (entry4 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (columnFrame 1 w).assignment)) = _
  rw [rawRow4, frame_eq, source7_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values4, frame, source7Values, combinedHighPad]

theorem columns5 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry5 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeColumnAssignment 1 w))) =
      plainPad (source4.map (Expression.eval (Verification.environment w))) := by
  change (entry5 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (columnFrame 1 w).assignment)) = _
  rw [rawRow5, frame_eq, source4_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values5, frame, source4Values, plainPad]

end Airbender.Blake2Round.Proofs.NativeColumnRows1Part1
