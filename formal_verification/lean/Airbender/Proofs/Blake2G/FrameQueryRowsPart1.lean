import Airbender.Proofs.Blake2G.FrameQueryValues
import Airbender.Proofs.Arithmetic.ExpressionRows
import Airbender.Proofs.Blake2G.FrameQueryArithmetic

namespace Airbender.Blake2G.Proofs.FrameQueryShapes
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000




theorem rawRow3 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry3 table).map (Expression.eval (Verification.environment f.assignment)) = values3 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [entry3, values3, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base,
    carryLow_as_value] <;> ring)




theorem rawRow4 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry4 table).map (Expression.eval (Verification.environment f.assignment)) = values4 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [entry4, values4, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base]




theorem rawRow5 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry5 table).map (Expression.eval (Verification.environment f.assignment)) = values5 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [entry5, values5, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base]

end Airbender.Blake2G.Proofs.FrameQueryShapes
