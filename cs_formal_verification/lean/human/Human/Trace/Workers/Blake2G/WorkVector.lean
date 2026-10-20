import Human.Trace.Workers.Blake2G.Call
import Human.Trace.Workers.Blake2Round.Compression
import Batteries.Data.Fin.Fold

namespace Airbender.Blake2G.WorkVector
open Arithmetic Trace Reference.RiscV.Sail

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

/-- Actual public pointers, initialized input/message words, and result words
    read from the same final Sail state exposed by `Delegation.TraceMapping`.
    The theorem proves these reads and bounds; none are caller premises. -/
structure WordMapping (initial after : State) (statePointer messagePointer : BitVec 32)
    (input message output : Vector Word 16) : Prop where
  /-- The caller's initial architectural pointers. -/
  pointers : (Cell.register 10).read initial = .ok statePointer initial ∧
    (Cell.register 11).read initial = .ok messagePointer initial
  /-- The initial working block in actual initialized RAM. -/
  inputWords : Blake2Round.Compression.WordsAt initial statePointer 0 input
  /-- The readonly message block in actual initialized RAM. -/
  messageWords : Blake2Round.Compression.WordsAt initial messagePointer 0 message
  /-- The final working block in actual RAM. -/
  outputWords : Blake2Round.Compression.WordsAt after statePointer 0 output
  /-- Message words retain their initial values. -/
  messageUnchanged : Blake2Round.Compression.WordsAt after messagePointer 0 message

end Airbender.Blake2G.WorkVector
