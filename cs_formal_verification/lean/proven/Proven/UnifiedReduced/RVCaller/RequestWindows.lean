module
public import Proven.UnifiedReduced.RVCaller.RequestTrace
public import Proven.Delegation.RequestWindows

@[expose] public section

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic
set_option warningAsError true

theorem rv_request_windows [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RVRequestTrace p} {before : RV.State} {addresses : List (BitVec 32)}
    (accepted : RVRequestChecks data) (inputs : RVRequestInputs data before addresses)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) :
    Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper := by
  have binding := rv_request_binding hp inverse accepted inputs
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
