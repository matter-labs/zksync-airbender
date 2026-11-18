module
public import Human.Trace.Workers.Blake2Round.Compression
public import Batteries.Data.Fin.Fold
public import Human.Circuits.Blake2G.Execution
public import Human.Circuits.Blake2G.Protocol

@[expose] public section

namespace Airbender.Blake2G.WorkVector
open Arithmetic Trace

/-- One original Clean G, with lanes and SIGMA words selected by the pinned
    project caller's controller. The state/message indices come from the same
    existing schedule used by the extended-round reference. No witness enters
    this computation. -/
def step (reduced : Bool) (call : Nat) (message : Vector Word 16)
    (state : Vector Nat 16) : Vector Nat 16 :=
  let control := Control.step (controllerAt reduced call)
  let lane (i : Fin 4) := Fin.ofNat 16 control.stateOffsets[i]
  Specs.BLAKE3.g state (lane 0) (lane 1) (lane 2) (lane 3)
    message[Fin.ofNat 16 control.messageOffsets[0]].value
    message[Fin.ofNat 16 control.messageOffsets[1]].value

/-- The G-only ABI updates a supplied sixteen-word work vector through all
    56 or 80 calls. Preparation and digest chaining belong to the caller;
    this function describes only its G span. -/
def run (reduced : Bool) (input message : Vector Word 16) : Vector Nat 16 :=
  Fin.foldl (callCount reduced) (fun state call => step reduced call.val message state)
    (input.map Word.value)

end Airbender.Blake2G.WorkVector
