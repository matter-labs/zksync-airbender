import Airbender.Review.Helpers.Memory.ReducedMachineCSRRequests

namespace Airbender.ReducedMachine.Native
open Trace Reference.RiscV.Sail
set_option autoImplicit false

/-- The native caller argument's observed request and raw timestamp pair.
    This is not a worker issuance or cryptographic accounting certificate. -/
structure CSRCallerObservation where
  request : CSRRequest
  time : ZMod mersenne31Modulus × ZMod mersenne31Modulus

def csrCallerObservation (row : Row mersenne31Modulus NativeReducedFamily) : CSRCallerObservation :=
  let request := csrRequest row.assignment
  let base := row.start.timestamp
  ⟨request,(base.1 + request.clockOffset,base.2)⟩

def CSRCallerObservation.clock (caller : CSRCallerObservation) : Nat :=
  (timeOfPair caller.time).value

/-- Filter by the actual imported multiplicity, retaining original rows.
    Zero-multiplicity rows still participate in the full native history. -/
def csrCallerRows (rows : List (Row mersenne31Modulus NativeReducedFamily)) :=
  rows.filter (fun row => decide ((csrRequest row.assignment).multiplicity = 1))

def csrCallers (rows : List (Row mersenne31Modulus NativeReducedFamily)) : List CSRCallerObservation :=
  (csrCallerRows rows).map csrCallerObservation

/-- Derived chronological caller observations. Clock and source/request facts
    are conclusions of native constraints and initialized history; the worker
    stream, fulfillment, converse and protocol/cryptographic enforcement are separate. -/
def CSRCallerProjection (trace : Data mersenne31Modulus NativeReducedFamily)
    (callers : List CSRCallerObservation) : Prop :=
  ∃ rows : List (Row mersenne31Modulus NativeReducedFamily),
    rows.Perm trace.rows ∧ rows.Pairwise (fun a b => b.clock < a.clock) ∧
    callers = csrCallers rows ∧
    callers.Pairwise (fun a b => b.clock < a.clock) ∧
    ∀ caller ∈ callers,
      caller.request.multiplicity = 1 ∧ caller.request.kind = 1991 ∧
      (∃ offset, caller.request.offsetHigh = some offset ∧ offset.val < 65536) ∧
      (timeOfPair caller.time).Bounded ∧ caller.clock % 4 = 3 ∧ 0 < caller.clock ∧
      ∃ row ∈ rows, caller = csrCallerObservation row ∧
        caller.clock = row.clock + 3 ∧
        caller.clock < (timeOfPair row.finish.timestamp).value ∧
        ∀ port ∈ row.ports, row.clock + port.clock.offset < caller.clock

end Airbender.ReducedMachine.Native
