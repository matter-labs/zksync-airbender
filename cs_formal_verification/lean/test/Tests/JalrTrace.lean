module
public import Tests.JumpHistory
public import Slop.JumpBranchSlt.Trace
public import Slop.Trace.Terminal
public import Human.Circuits.JumpBranchSlt.Jump
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump

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
