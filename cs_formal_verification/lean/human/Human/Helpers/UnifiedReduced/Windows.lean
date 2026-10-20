import Human.Helpers.Delegation.BoundaryMemory
import Human.Helpers.UnifiedReduced.MixedMemory
import Human.Helpers.Delegation.RequestWindows

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Complete actual machine rows starting between two instruction-boundary cuts. -/
def RequestTrace.windowMachineRows [Fact p.Prime] (data : RequestTrace p) (lower upper : Nat) :=
  data.machine.rows.filter fun row => decide
    (lower ≤ Delegation.Caller.startClock row ∧ Delegation.Caller.startClock row < upper)

/-- Architectural machine ports and complete worker rows in the same native window.
    The callers' virtual CSR ports remain in request matching. -/
def RequestTrace.windowSteps [Fact p.Prime] (data : RequestTrace p) (lower upper : Nat) :=
  (data.windowMachineRows lower upper).flatMap (fun row => (machinePorts row).toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)) ++
    (data.workers.windowRows lower upper).flatMap Delegation.Row.memorySteps

/-- Native writes strictly before the instruction cut, including zero-clock
    workers. Clean event clocks add one to reserve time zero for seeds. -/
def RequestTrace.prefixSteps [Fact p.Prime] (data : RequestTrace p) (cutoff : Nat) :=
  data.mixedSteps.filter fun edge => decide ((timeOfPair edge.2.time).value < cutoff)

/-- Actual Sail cell reads and canonical native tokens at a derived cut.
    Raw timestamps are retained rather than reset to initialization time zero. -/
def NativeBoundary (tokens : List (MemoryToken p)) (state : State) (cells : List Cell) : Prop :=
  Delegation.BoundaryImage tokens state cells ∧
    ∀ token ∈ tokens, token.word.Bounded ∧ (timeOfPair token.time).Bounded

end Airbender.UnifiedReduced.Caller
