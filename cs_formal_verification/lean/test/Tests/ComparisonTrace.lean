module
public import Tests.Comparison
public import Tests.JumpHistory

@[expose] public section

namespace Tests.ComparisonTrace
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 32768

-- All four comparisons of zero with -1, with rd aliasing the selected source.
private def assignment (signed immediate : Bool) (i : Nat) : ZMod babyBearModulus :=
  if i = 2 then 4 else if i = 18 then 8
  else if i = 28 || i = 29 then (if immediate then 0 else 65535)
  else if i = 32 then (if immediate then 4 else 5)
  else if i = 49 || i = 50 || i = 51 then 1
  else Comparison.edgeRow signed immediate false i

private def seed : List (MemoryToken babyBearModulus) :=
  [Cell.initialToken (.register 0) 0, Cell.initialToken (.register 1) 0,
    Cell.initialToken (.register 2) 0xffffffff]
private def row (signed immediate : Bool) : Row babyBearModulus JumpBranchSlt.TraceKind :=
  ⟨.jumpBranchSlt, assignment signed immediate⟩

private def token (index clock value : Nat) : MemoryToken babyBearModulus :=
  ⟨(Cell.register (BitVec.ofNat 5 index)).addressCode, (clock, 0), value⟩

private def trace (signed immediate : Bool) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    JumpBranchSlt.NativeTrace babyBearModulus where
  rows := [row signed immediate]
  rom := rom
  initial := (row signed immediate).start
  terminal := (row signed immediate).finish
  initialMemory := seed
  terminalMemory := if immediate then
    [token 0 5 0, token 1 6 (Nat.pair (if signed then 0 else 1) 0), token 2 0 (Nat.pair 65535 65535)]
    else [token 0 0 0, token 1 4 0, token 2 6 (Nat.pair (if signed then 0 else 1) 0)]

private theorem boundary (signed immediate : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) : ClockBoundary (trace signed immediate rom) := by
  constructor
  · cases signed <;> cases immediate <;> change 4 < timestampBase ∧ 0 < timestampBase
    all_goals constructor <;> decide
  · cases signed <;> cases immediate <;> change 4 % 4 = 0
    all_goals decide
  · intro actual member
    simp only [trace, seed, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide

end Tests.ComparisonTrace
