module
public import Slop.ShiftBinop.Claims
public import Tests.ShiftBinopTimestamp
import all Init.Data.Array.DecidableEq -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)
import all Init.Data.Vector.Basic -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)

@[expose] public section

namespace Tests.ShiftBinopImmediate
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

-- XORI x1,x0,-1: exercise both packed immediate bytes and the upper sign bytes.
def assignment (i : Nat) : ZMod babyBearModulus :=
  if i = 8 ∨ i = 9 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨
      i = 52 ∨ i = 53 ∨ i = 57 ∨ i = 58 ∨ i = 66 ∨ i = 67 ∨
      i = 75 ∨ i = 76 ∨ i = 84 ∨ i = 85 then 255
  else if i = 31 ∨ i = 32 then 65535
  else Tests.ShiftBinopTimestamp.assignment false i

theorem constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment assignment)
    Airbender.ShiftBinop.importedConstraints := by
  simp [Airbender.ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, assignment, Tests.ShiftBinopTimestamp.assignment,
    Tests.ShiftBinop.row]
  repeat' apply And.intro
  all_goals solve
    | decide
    | (apply Verification.range16_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 524545,
         (#v[255, 255, 0, 0, 0, 0, 0, 0, 0, 3] : Vector (ZMod babyBearModulus) 10) =
           (Verification.shiftBinopRow i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       refine ⟨⟨256, by decide⟩, ?_⟩
       have shape : Verification.shiftBinopRow ⟨256, by decide⟩ =
           (#v[255, 255, 0, 0, 0, 0, 0, 0, 0, 3] : Vector Nat 10) := by decide
       rw [shape]
       apply Vector.ext
       intro j bound
       rw [Vector.getElem_map]
       interval_cases j <;> norm_num)
    | (with_unfolding_all change ∃ i : Fin 524545,
         (#v[0, 255, 255, 0, 0, 0, 0, 0, 0, 4] : Vector (ZMod babyBearModulus) 10) =
           (Verification.shiftBinopRow i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       refine ⟨⟨512, by decide⟩, ?_⟩
       have shape : Verification.shiftBinopRow ⟨512, by decide⟩ =
           (#v[0, 255, 255, 0, 0, 0, 0, 0, 0, 4] : Vector Nat 10) := by decide
       rw [shape]
       apply Vector.ext
       intro j bound
       rw [Vector.getElem_map]
       interval_cases j <;> norm_num)

private theorem clock_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) Airbender.ShiftBinop.clockConstraints := by
  apply Verification.holds_append (left := Airbender.ShiftBinop.importedConstraints)
    (right := Airbender.ShiftBinop.importedConstraintsTimestampLookups)
  · exact constraints
  · simp [Airbender.ShiftBinop.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    repeat' apply And.intro
    all_goals apply Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment,
      Tests.ShiftBinopTimestamp.assignment, Tests.ShiftBinop.row]
    all_goals decide

private def seed : List (MemoryToken babyBearModulus) :=
  [Cell.initialToken (.register 0) 0, Cell.initialToken (.register 1) 0]
private def row : Row babyBearModulus Airbender.ShiftBinop.TraceKind :=
  ⟨.shiftBinop, assignment⟩

private def trace (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Airbender.ShiftBinop.NativeTrace babyBearModulus where
  rows := [row]
  rom := rom
  initial := row.start
  terminal := row.finish
  initialMemory := seed
  terminalMemory := [⟨(Cell.register 0).addressCode, (5, 0), 0⟩,
    ⟨(Cell.register 1).addressCode, (6, 0), Nat.pair 65535 65535⟩]

private theorem accepted (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Accepted (trace rom) := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact clock_constraints
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · dsimp [trace, Row.reads, Row.writes, Row.ports, Row.columns, row,
      Airbender.ShiftBinop.importedConstraintsMemoryPorts,
      Airbender.ShiftBinop.importedConstraintsTraceColumns]
    decide

private theorem boundary (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ClockBoundary (trace rom) := by
  constructor
  · change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro actual member
    simp only [trace, seed, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> constructor <;> decide

end Tests.ShiftBinopImmediate
