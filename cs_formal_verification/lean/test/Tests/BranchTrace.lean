module
public import Tests.Branch
public import Tests.JumpHistory

@[expose] public section

namespace Tests.BranchTrace
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 32768

private def assignment (tag : Fin 6) (wrap : Bool) (i : Nat) : ZMod babyBearModulus :=
  if i = 2 then 4 else if i = 18 then 8
  else if i = 49 || i = 50 || i = 51 then 1
  else Branch.row tag wrap i

private def seed : List (MemoryToken babyBearModulus) :=
  [Cell.initialToken (.register 0) 0, Cell.initialToken (.register 1) 0,
    Cell.initialToken (.register 2) 0xffffffff]
private def row (tag : Fin 6) (wrap : Bool) : Row babyBearModulus JumpBranchSlt.TraceKind :=
  ⟨.jumpBranchSlt, assignment tag wrap⟩

private def trace (tag : Fin 6) (wrap : Bool) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    JumpBranchSlt.NativeTrace babyBearModulus where
  rows := [row tag wrap]
  rom := rom
  initial := (row tag wrap).start
  terminal := (row tag wrap).finish
  initialMemory := seed
  terminalMemory := [⟨(Cell.register 1).addressCode, (4, 0), 0⟩,
    ⟨(Cell.register 2).addressCode, (5, 0), Nat.pair 65535 65535⟩,
    ⟨(Cell.register 0).addressCode, (6, 0), 0⟩]

private theorem boundary (tag : Fin 6) (wrap : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) : ClockBoundary (trace tag wrap rom) := by
  constructor
  · fin_cases tag <;> cases wrap <;> change 4 < timestampBase ∧ 0 < timestampBase
    all_goals constructor <;> decide
  · fin_cases tag <;> cases wrap <;> change 4 % 4 = 0
    all_goals decide
  · intro actual member
    simp only [trace, seed, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide

end Tests.BranchTrace
