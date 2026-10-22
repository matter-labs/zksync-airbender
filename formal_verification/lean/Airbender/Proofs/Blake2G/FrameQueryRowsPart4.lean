import Airbender.Proofs.Blake2G.FrameQueryValues
import Airbender.Proofs.Arithmetic.ExpressionRows
import Airbender.Proofs.Blake2G.FrameQueryArithmetic

namespace Airbender.Blake2G.Proofs.FrameQueryShapes
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000




theorem rawRow12 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry12 table).map (Expression.eval (Verification.environment f.assignment)) = values12 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [entry12, values12, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base]




theorem rawRow13 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry13 table).map (Expression.eval (Verification.environment f.assignment)) = values13 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [entry13, values13, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base,
    carryLow_as_value, combinedLow_as_value] <;> ring)




theorem rawRow14 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry14 table).map (Expression.eval (Verification.environment f.assignment)) = values14 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [entry14, values14, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base,
    combinedLow_as_value]

end Airbender.Blake2G.Proofs.FrameQueryShapes
