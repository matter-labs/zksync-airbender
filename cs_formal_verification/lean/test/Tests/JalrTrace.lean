module
public import Tests.JumpSailHistory
public import Slop.JumpBranchSlt.Claims

@[expose] public section

namespace Tests.JalrTrace
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 32768

-- JALR x1,-4(x1): the old source is five, the link is four, and target is zero.
private def assignment (i : Nat) : ZMod babyBearModulus :=
  if i = 5 then 1 else if i = 11 then 0 else if i = 12 then 1
  else if i = 16 || i = 17 || i = 24 then 0
  else if i = 22 then 5 else if i = 32 then 4
  else if i = 36 || i = 39 || i = 40 then 1
  else JumpHistory.assignment 5 false i

private def seed : List (MemoryToken babyBearModulus) :=
  [Cell.initialToken (.register 0) 0, Cell.initialToken (.register 1) 5]
private def row : Row babyBearModulus JumpBranchSlt.TraceKind := ⟨.jumpBranchSlt, assignment⟩

private def trace (rom : Table (ZMod babyBearModulus) (fields 9)) :
    JumpBranchSlt.NativeTrace babyBearModulus where
  rows := [row]
  rom := rom
  initial := row.start
  terminal := row.finish
  initialMemory := seed
  terminalMemory := [⟨(Cell.register 0).addressCode, (5, 0), Nat.pair 0 0⟩,
    ⟨(Cell.register 1).addressCode, (6, 0), Nat.pair 4 0⟩]

/-- The honest inputs: JALR from x1 = 5 with `JumpHistory`'s clock; the second port reads
    at clock 0 and the third at 4. -/
private def witness : JumpBranchSlt.Completeness.Inputs :=
  { JumpHistory.witness false with sel := 1, rs1 := 1, aLo := 5, oldLo := 5, prev1Lo := 0, prev2Lo := 4 }

private theorem constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) JumpBranchSlt.clockConstraints :=
  JumpBranchSlt.Completeness.clock_complete_of_agree witness
    (by constructor <;> decide) (by constructor <;> decide) (by decide)

private theorem accepted (rom : Table (ZMod babyBearModulus) (fields 9)) : Accepted (trace rom) := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact constraints
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · dsimp [trace, Row.reads, Row.writes, Row.ports, Row.columns, row,
      JumpBranchSlt.importedConstraintsMemoryPorts, JumpBranchSlt.importedConstraintsTraceColumns]
    decide

private theorem boundary (rom : Table (ZMod babyBearModulus) (fields 9)) : ClockBoundary (trace rom) := by
  constructor
  · change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro actual member
    simp only [trace, seed, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> constructor <;> decide

end Tests.JalrTrace
