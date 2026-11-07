import Airbender.Review.Circuits.Blake2G.Tables.Setup
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Blake2G.FrameQueryBindings
import Airbender.Proofs.Blake2G.FrameQueryRows
import Airbender.Proofs.Blake2Round.NativeColumnView1
import Airbender.Proofs.Blake2Round.NativeXorPadDefinitions

namespace Airbender.Blake2Round.Proofs.NativeColumnRows1Part0
open Blake2G.Proofs.FrameQueryShapes NativeColumnView1
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem columns0 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry0 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeColumnAssignment 1 w))) =
      carryPad 0 (source0.map (Expression.eval (Verification.environment w))) := by
  change (entry0 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (columnFrame 1 w).assignment)) = _
  rw [rawRow0, frame_eq, source0_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values0, frame, source0Values, carryPad]

theorem columns1 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry1 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeColumnAssignment 1 w))) =
      plainPad (source1.map (Expression.eval (Verification.environment w))) := by
  change (entry1 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (columnFrame 1 w).assignment)) = _
  rw [rawRow1, frame_eq, source1_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [values1, frame, source1Values, plainPad] <;> ring)

theorem columns2 {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (w : Nat → ZMod p) :
    (entry2 (Blake2G.setupTable control)).map
        (Expression.eval (Verification.environment (nativeColumnAssignment 1 w))) =
      carryPad 0 (source2.map (Expression.eval (Verification.environment w))) := by
  change (entry2 (Blake2G.setupTable control)).map
    (Expression.eval (Verification.environment (columnFrame 1 w).assignment)) = _
  rw [rawRow2, frame_eq, source2_eval]
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [values2, frame, source2Values, carryPad]

end Airbender.Blake2Round.Proofs.NativeColumnRows1Part0
