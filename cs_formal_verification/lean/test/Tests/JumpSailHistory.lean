module
public import Tests.JumpHistory
public import Slop.JumpBranchSlt.Trace
public import Slop.Trace.Terminal
public import Human.Circuits.JumpBranchSlt.Jump
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.JumpBranchSlt.PortReads

@[expose] public section

namespace Tests.JumpSailHistory
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 32768

-- JAL x1,-4 and JAL x0,-4. All three x0 ports in the discarded form
-- retain the latest preceding native clock; public x1 starts at five.
def assignment (discarded : Bool) (i : Nat) : ZMod babyBearModulus :=
  if discarded && (i = 7 || i = 28 || i = 30) then 0
  else if discarded && i = 15 then 1
  else if discarded && i = 32 then 5
  else JumpHistory.assignment 5 false i

def row (discarded : Bool) : Row babyBearModulus JumpBranchSlt.TraceKind :=
  ⟨.jumpBranchSlt, assignment discarded⟩

def seed : List (MemoryToken babyBearModulus) :=
  [Cell.initialToken (.register 0) 0, Cell.initialToken (.register 1) 5]

def token (index clock value : Nat) : MemoryToken babyBearModulus :=
  ⟨Nat.pair 0 (Nat.pair index 0), (clock, 0), Nat.pair value 0⟩

def trace (discarded : Bool) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    JumpBranchSlt.NativeTrace babyBearModulus where
  rows := [row discarded]
  rom := rom
  initial := (row discarded).start
  terminal := (row discarded).finish
  initialMemory := seed
  terminalMemory := if discarded then [token 0 6 0, token 1 0 5]
    else [token 0 5 0, token 1 6 4]

/-- The honest inputs: `JumpHistory`'s, discarding into x0 whose third port read is at 5. -/
private def witness (discarded : Bool) : JumpBranchSlt.Completeness.Inputs :=
  { JumpHistory.witness false with
    rdZero := discarded, rd := if discarded then 0 else 1, oldLo := if discarded then 0 else 5,
    prev2Lo := if discarded then 5 else 0 }

private theorem constraints (discarded : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment discarded)) JumpBranchSlt.clockConstraints :=
  JumpBranchSlt.Completeness.clock_complete_of_agree (witness discarded)
    (by cases discarded <;> constructor <;> decide) (by cases discarded <;> constructor <;> decide)
    (by cases discarded <;> decide)

private theorem accepted (discarded : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) : Accepted (trace discarded rom) := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact constraints discarded
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    cases discarded <;> rfl
  · exact List.Perm.swap _ _ []
  · cases discarded <;> dsimp [trace, Row.reads, Row.writes, Row.ports, Row.columns,
      row, JumpBranchSlt.importedConstraintsMemoryPorts, JumpBranchSlt.importedConstraintsTraceColumns]
    all_goals decide

private theorem boundary (discarded : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) : ClockBoundary (trace discarded rom) := by
  constructor
  · cases discarded <;>
      change 4 < timestampBase ∧ 0 < timestampBase
    all_goals constructor <;> decide
  · cases discarded <;> change 4 % 4 = 0
    all_goals decide
  · intro actual member
    simp only [trace, seed, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> constructor <;> decide

-- Flip the high-PC wrap bit and use its field-aliased result. Neither the
-- incoming decoder nor the register history ranges the external terminal PC.
private def noncanonicalAssignment (i : Nat) : ZMod babyBearModulus :=
  if i = 17 then -1 else if i = 40 then 1 else assignment false i

private theorem noncanonical_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment noncanonicalAssignment) JumpBranchSlt.clockConstraints := by
  have core := Verification.holds_of_sublist (constraints false)
    (List.sublist_append_left JumpBranchSlt.importedConstraints
      JumpBranchSlt.importedConstraintsTimestampLookups)
  apply Verification.holds_append (left := JumpBranchSlt.importedConstraints)
    (right := JumpBranchSlt.importedConstraintsTimestampLookups)
  · have high : (65535 + 1 + -65536 : ZMod babyBearModulus) = 0 := by decide
    simpa [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Lookup.Contains, Vector.map, Expression.eval, Verification.environment,
      noncanonicalAssignment, assignment, JumpHistory.assignment, Tests.JumpTimestamp.assignment,
      Verification.range16, Verification.pairLookup, Verification.jumpCleanup, high] using core
  · have timestamps := Verification.holds_of_sublist (constraints false)
      (List.sublist_append_right JumpBranchSlt.importedConstraints
        JumpBranchSlt.importedConstraintsTimestampLookups)
    simpa [JumpBranchSlt.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
      Lookup.Contains, timestampLookup, Vector.map, Expression.eval, Verification.environment,
      noncanonicalAssignment] using timestamps

/-- Native matching propagates public initial alignment to the entire trace. -/
theorem decoded_pc_alignment (discarded : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) :
    (∀ actual ∈ (trace discarded rom).rows,
      actual.start.word.lo % 4 = 0 ∧ actual.finish.word.lo % 4 = 0) ∧
      (trace discarded rom).terminal.word.lo % 4 = 0 :=
  JumpBranchSlt.Proofs.trace_pc_alignment (by decide) (accepted discarded rom)
    (by cases discarded <;> rfl)

end Tests.JumpSailHistory
