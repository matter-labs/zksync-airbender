import Airbender.Proofs.Arithmetic.ExpressionRows
import Airbender.Proofs.Blake2G.FrameQueryShapes

namespace Airbender.Blake2G.Proofs.FrameQueryShapes
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def entry6 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    Vector (Expression (ZMod p)) 9 :=
  show Vector (Expression (ZMod p)) table.toRaw.arity from
  #v[Arithmetic.linearExpression (0) [(-491520, 19), (491520, 55), (3932160, 56)],
      Arithmetic.linearExpression (0) [(-491520, 23), (-491520, 47), (-125829120, 48), (-16, 49), (491520, 51), (3932160, 52)],
      Arithmetic.linearExpression (0) [(1, 59)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (18) []]

theorem lookup6_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨6, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry6 table) := rfl

def values6 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[-491520 * f.inputs[2] + 491520 * f.bLow[0] + 3932160 * f.bMiddle[0], -491520 * f.inputs[4] - 491520 * f.firstDBytes[2] - 125829120 * f.firstDBytes[3] - 16 * f.cCarries[0] + 491520 * f.cLow[0] + 3932160 * f.cMiddle[0], f.packedB[0] - 16 * (combinedHigh f.packedB[0]), 0, 0, 0, 0, 0, 18]

theorem rawRow6 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry6 table).map (Expression.eval (Verification.environment f.assignment)) = values6 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals (simp [entry6, values6, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base,
    combinedLow_as_value] <;> ring)

def entry7 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    Vector (Expression (ZMod p)) 9 :=
  show Vector (Expression (ZMod p)) table.toRaw.arity from
  #v[Arithmetic.linearExpression (0) [(1, 60)],
      Arithmetic.linearExpression (0) [(1, 53)],
      Arithmetic.linearExpression (0) [(1, 62)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (17) []]

theorem lookup7_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨7, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry7 table) := rfl

def values7 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.bLow[1], f.cLow[1], (combinedHigh f.packedB[0]), 0, 0, 0, 0, 0, 17]

theorem rawRow7 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry7 table).map (Expression.eval (Verification.environment f.assignment)) = values7 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [entry7, values7, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base]

def entry8 {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    Vector (Expression (ZMod p)) 9 :=
  show Vector (Expression (ZMod p)) table.toRaw.arity from
  #v[Arithmetic.linearExpression (0) [(1, 61)],
      Arithmetic.linearExpression (0) [(1, 54)],
      Arithmetic.linearExpression (0) [(1, 63)],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (0) [],
      Arithmetic.linearExpression (20) []]

theorem lookup8_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨8, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry8 table) := rfl

def values8 {p : Nat} (f : Frame p) : Vector (ZMod p) 9 :=
  #v[f.bMiddle[1], f.cMiddle[1], f.firstBMiddle[1], 0, 0, 0, 0, 0, 20]

theorem rawRow8 {p : Nat} [Fact p.Prime]
    (table : Table (ZMod p) (fields 9)) (f : Frame p) :
    (entry8 table).map (Expression.eval (Verification.environment f.assignment)) = values8 f := by
  apply Vector.ext
  intro lane bound
  change lane < 9 at bound
  interval_cases lane
  all_goals simp [entry8, values8, Arithmetic.linearExpression, Expression.eval, Verification.environment, Frame.assignment, assemble, Frame.base]

end Airbender.Blake2G.Proofs.FrameQueryShapes
