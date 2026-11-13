module
public import Tests.TraceMemory
public import Human.Helpers.Core.BabyBearPrime
public import Proven.AddSub.Selectors
public import Proven.JumpBranchSlt.Branch
public import Proven.JumpBranchSlt.Jump
public import Proven.MulDiv.Values
public import Proven.ShiftBinop.Ports
public import Proven.SubwordMemory.Values
public import Proven.Trace.Family.Values
public import Proven.Trace.Pooled
public import Proven.Trace.RowContext

@[expose] public section

namespace Tests.TraceExecution
open Airbender Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def cells : List Cell :=
  [.register 0, .register 1, .register 2, .register 3, .register 4, .register 5, .register 6, .register 7, .register 8, .register 9, .register 10, .register 11, .register 12, .register 13, .register 14, .register 15, .register 16, .register 17, .register 18, .register 19, .register 20, .register 21, .register 22, .register 23, .register 24, .register 25, .register 26, .register 27, .register 28, .register 29, .register 30, .register 31]

private def initial : List (MemoryToken babyBearModulus) :=
  (List.range 32).map fun index =>
    ⟨Nat.pair 0 (Nat.pair index 0), (0, 0), Nat.pair (if index = 1 then 5 else 0) 0⟩

private def trace : Data babyBearModulus :=
  { Tests.TraceMemory.twoRows Tests.TraceMemory.publicROM with
    initialMemory := initial
    terminalMemory := (Tests.TraceMemory.twoRows Tests.TraceMemory.publicROM).terminalMemory ++ initial.drop 3
    rom := ROM.table cells initial }

private theorem accepted : Accepted trace := by
  have old := Tests.TraceMemory.two_accepted Tests.TraceMemory.publicROM
  refine ⟨?_, old.active, old.states, ?_⟩
  · intro actual member
    rcases List.mem_cons.mp member with rfl | present
    · exact Tests.TraceMemory.second_satisfies
    · have same := List.mem_singleton.mp present
      subst actual
      exact Tests.TraceMemory.local_satisfies
  · decide

end Tests.TraceExecution
