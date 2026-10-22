import Airbender.Proofs.Arithmetic.ExpressionRows
import Airbender.Proofs.Blake2G.FrameQueryShapes

namespace Airbender.Blake2G.Proofs.FrameQueryShapes
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def entry9 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    Vector (Expression (ZMod p)) 9 :=
  show Vector (Expression (ZMod p)) table.toRaw.arity from
  #v[Arithmetic.linearExpression (0) [(-491520, 20), (491520, 60), (3932160, 61)],
      Arithmetic.linearExpression (0) [(-491520, 24), (-491520, 44), (-125829120, 45), (-491520, 49), (-16, 50), (491520, 53), (3932160, 54)],
      Arithmetic.linearExpression (0) [(1, 64)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (18) []]

theorem lookup9_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨9, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry9 table) := rfl

def values9 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[-491520 * f.inputs[3] + 491520 * f.bLow[1] + 3932160 * f.bMiddle[1], -491520 * f.inputs[5] - 491520 * f.firstDBytes[0] - 125829120 * f.firstDBytes[1] - 491520 * f.cCarries[0] - 16 * f.cCarries[1] + 491520 * f.cLow[1] + 3932160 * f.cMiddle[1], f.packedB[1] - 16 * (combinedHigh f.packedB[1]), 0, 0, 0, 0, 0, 18]

theorem rawRow9 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry9 table).map (Expression.eval (Verification.environment f.assignment)) = values9 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [entry9, values9, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base,
    combinedLow_as_value] <;> ring)

def entry10 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    Vector (Expression (ZMod p)) 9 :=
  show Vector (Expression (ZMod p)) table.toRaw.arity from
  #v[Arithmetic.linearExpression (0) [(1, 47)],
      Arithmetic.linearExpression (0) [(1, 69)],
      Arithmetic.linearExpression (0) [(1, 71)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem lookup10_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨10, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry10 table) := rfl

def values10 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.firstDBytes[2], f.secondABytes[0], f.secondDBytes[0], 0, 0, 0, 0, 0, 4]

theorem rawRow10 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry10 table).map (Expression.eval (Verification.environment f.assignment)) = values10 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [entry10, values10, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base]

def entry11 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    Vector (Expression (ZMod p)) 9 :=
  show Vector (Expression (ZMod p)) table.toRaw.arity from
  #v[Arithmetic.linearExpression (0) [(1, 48)],
      Arithmetic.linearExpression (0) [(-7864320, 15), (-7864320, 19), (-7864320, 33), (-7864320, 35), (-256, 37), (-512, 38), (-7864320, 59), (-125829120, 62), (-1006632960, 63), (-256, 65), (-512, 66), (7864320, 69)],
      Arithmetic.linearExpression (0) [(1, 72)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (4) []]

theorem lookup11_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨11, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry11 table) := rfl

def values11 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.firstDBytes[3], -7864320 * f.inputs[0] - 7864320 * f.inputs[2] - 7864320 * f.inputs[8] - 7864320 * f.inputs[10] - 256 * f.addCarries[0] - 7864320 * f.packedB[0] - 1006632960 * f.firstBMiddle[1] - 256 * f.addCarries[2] + 7864320 * f.secondABytes[0], f.secondDBytes[1], 0, 0, 0, 0, 0, 4]

theorem rawRow11 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry11 table).map (Expression.eval (Verification.environment f.assignment)) = values11 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [entry11, values11, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base,
    carryLow_as_value, combinedLow_as_value] <;> ring)

end Airbender.Blake2G.Proofs.FrameQueryShapes
