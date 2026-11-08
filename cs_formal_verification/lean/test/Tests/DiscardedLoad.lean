import Tests.TraceExecution
import Tests.TraceZeroRegister
import Human.Circuits.AddSub.RowInput
import Human.Helpers.Core.CircuitOutput
import Mathlib.Tactic.IntervalCases
import Slop.KernelRfl

namespace Tests.DiscardedLoad
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private def cells : List Cell := Tests.TraceExecution.cells
private def initial : List (MemoryToken babyBearModulus) :=
  (List.range 32).map fun index =>
    ⟨Nat.pair 0 (Nat.pair index 0), (0, 0), if index = 1 then Nat.pair 0 64 else 0⟩
private def trace : Data babyBearModulus where
  rows := [Tests.TraceZeroRegister.row]
  rom := ROM.table cells initial
  initial := Tests.TraceZeroRegister.row.start
  terminal := Tests.TraceZeroRegister.row.finish
  initialMemory := initial
  terminalMemory := ⟨0, (6, 0), 0⟩ :: initial.drop 1
private theorem accepted : Accepted trace := by
  constructor
  · intro row present
    have same := List.mem_singleton.mp present
    subst row
    exact Tests.TraceZeroRegister.local_satisfies
  · intro row present
    have same := List.mem_singleton.mp present
    subst row
    rfl
  · exact List.Perm.swap _ _ []
  · decide

end Tests.DiscardedLoad
