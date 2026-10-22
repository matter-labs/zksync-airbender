import Airbender.Proofs.Arithmetic.ExpressionRows
import Airbender.Proofs.Blake2G.FrameQueryShapes

namespace Airbender.Blake2G.Proofs.FrameQueryShapes
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def entry12 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    Vector (Expression (ZMod p)) 9 :=
  show Vector (Expression (ZMod p)) table.toRaw.arity from
  #v[Arithmetic.linearExpression (0) [(1, 44)],
      Arithmetic.linearExpression (0) [(1, 70)],
      Arithmetic.linearExpression (0) [(1, 73)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem lookup12_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨12, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry12 table) := rfl

def values12 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.firstDBytes[0], f.secondABytes[1], f.secondDBytes[2], 0, 0, 0, 0, 0, 4]

theorem rawRow12 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry12 table).map (Expression.eval (Verification.environment f.assignment)) = values12 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [entry12, values12, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base]

def entry13 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    Vector (Expression (ZMod p)) 9 :=
  show Vector (Expression (ZMod p)) table.toRaw.arity from
  #v[Arithmetic.linearExpression (0) [(1, 45)],
      Arithmetic.linearExpression (0) [(-7864320, 16), (-7864320, 20), (-7864320, 34), (-7864320, 36), (-7864320, 37), (-15728640, 38), (-256, 39), (-512, 40), (-125829120, 57), (-1006632960, 58), (-7864320, 64), (-7864320, 65), (-15728640, 66), (-256, 67), (-512, 68), (7864320, 70)],
      Arithmetic.linearExpression (0) [(1, 74)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem lookup13_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨13, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry13 table) := rfl

def values13 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.firstDBytes[1], -7864320 * f.inputs[1] - 7864320 * f.inputs[3] - 7864320 * f.inputs[9] - 7864320 * f.inputs[11] - 7864320 * f.addCarries[0] - 256 * f.addCarries[1] - 1006632960 * f.firstBMiddle[0] - 7864320 * f.packedB[1] - 7864320 * f.addCarries[2] - 256 * f.addCarries[3] + 7864320 * f.secondABytes[1], f.secondDBytes[3], 0, 0, 0, 0, 0, 4]

theorem rawRow13 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry13 table).map (Expression.eval (Verification.environment f.assignment)) = values13 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [entry13, values13, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base,
    carryLow_as_value, combinedLow_as_value] <;> ring)

def entry14 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    Vector (Expression (ZMod p)) 9 :=
  show Vector (Expression (ZMod p)) table.toRaw.arity from
  #v[Arithmetic.linearExpression (0) [(1, 59), (16, 62)],
      Arithmetic.linearExpression (0) [(1, 77)],
      Arithmetic.linearExpression (0) [(1, 79)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (19) []]

theorem lookup14_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨14, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry14 table) := rfl

def values14 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.packedB[0], f.secondCLow[0], f.secondBChunks[0], 0, 0, 0, 0, 0, 19]

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
