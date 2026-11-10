import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.UnifiedReduced.RequestTrace
import Airbender.Proofs.Delegation.RequestWindows

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic
set_option warningAsError true

theorem request_windows [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) :
    Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper := by
  have binding := request_binding hp inverse accepted inputs
  have clocks := Trace.Proofs.state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned
  apply Delegation.Caller.Proofs.request_window (by omega)
    (⟨binding.fulfilled, binding.clocks, ?_, ?_, ?_, binding.invocations.1⟩ :
      Delegation.Caller.Proofs.WindowFacts data.callers data.workers) first last pastZero
  · intro caller member
    obtain ⟨worker, matched, _⟩ := binding.workers caller member
    exact (congrArg (fun call : Delegation.Requests.Request p => (timeOfPair call.time).value)
      matched.2.1).symm.trans matched.2.2.invocation
  · intro caller member
    exact Trace.Proofs.ClockLaws.advance hp inverse data.machine.rom caller
      (accepted.constraints caller (List.mem_of_mem_filter member))
      (clocks caller (List.mem_of_mem_filter member)).1
  · intro caller member
    simpa [Delegation.Caller.startClock, Trace.Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod]
      using (clocks caller (List.mem_of_mem_filter member)).2

end Airbender.UnifiedReduced.Caller.Proofs
