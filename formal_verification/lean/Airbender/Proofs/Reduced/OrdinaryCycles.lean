import Airbender.Proofs.Reduced.CycleWindows
import Airbender.Proofs.Reduced.WordExecution

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail Delegation.Caller Delegation.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- Exact native cycle states and read bounds do not depend on the registry. -/
theorem ordinary_context_at
    {data : RequestTrace babyBearModulus} {program : List PooledProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : StreamMemoryInputs data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    (initialPositive : 0 < (timeOfPair data.machine.initial.timestamp).value)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    {row : Trace.Row babyBearModulus PooledFamily}
    (member : row ∈ data.machine.rows) (ordinary : row ∉ data.callers) :
    ∃ before after,
      SailHistory cells (events.filter fun event => decide
        (event.1 ≤ Delegation.Caller.startClock row)) initial before ∧
      SailHistory cells (events.filter fun event => decide
        (Delegation.Caller.startClock row < event.1 ∧
          event.1 ≤ Delegation.Caller.finishClock row)) before after ∧
      SailHistory cells (events.filter fun event => decide
        (Delegation.Caller.finishClock row < event.1)) after finalState ∧
      SailHistory cells (rowEvents 1 row).reverse before after ∧
      ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded := by
  have floor := machine_clock_floor (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram member
  have positive : 0 < Delegation.Caller.startClock row := lt_of_lt_of_le initialPositive floor
  have slots := Delegation.Caller.Proofs.worker_schedule (by decide) (by decide)
    accepted.toRequestChecks inputs.publicProgram effects.requests
  have clocks := machine_clock_facts (by decide) (by decide)
    accepted.toRequestChecks inputs.publicProgram member
  obtain ⟨before, after, _, past, current, future⟩ := history_window order history
    (by omega : Delegation.Caller.startClock row ≤ Delegation.Caller.finishClock row)
  have cycle := cycle_window_permutation (by decide) (by decide)
    accepted.toRequestChecks inputs.publicProgram effects.requests slots permutation member positive
  have native := ordinary_cycle_history (by decide) (by decide)
    accepted.toRequestChecks inputs.publicProgram member ordinary cycle
    (order.sublist List.filter_sublist) current
  refine ⟨before, after, past, current, future, native, ?_⟩
  intro port present
  exact (effects.words _ (mixed_machine_member member
    (by rwa [machine_ports_ordinary member ordinary]))).1


end Airbender.AddSub.Modular.External.Caller.Proofs
