import Airbender.Proofs.Blake2G.ReferenceCalls

namespace Airbender.Blake2G.Call
open Trace Reference.RiscV.Sail

/-- The existing complete public G span executes a sequence of independent
    successful reference micro-calls in the actual full Sail states. Each call
    includes its exact write footprint/frame. Controls, pointer ABI and operands
    are derived from accepted initialized history and the existing span profile.
    This is worker reference execution; mixed caller fetch/PC retirement and
    global worker participation are separate composition claims. -/
theorem execution_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {domain : List Cell} {reduced : Bool}
    (accepted : Delegation.MemoryAccepted data) (inputs : NativeCallInputs data initial domain reduced)
    (aligned : ∀ cell ∈ domain, cell.Aligned)
    (ram : ∀ address, Cell.ram address ∈ domain → ROM.limit ≤ address.toNat) :
    ∃ after, Relation.ReflTransGen Executes initial after ∧ Delegation.TraceMapping data initial after domain :=
  Proofs.span_reference hp inverse accepted inputs.toBoundaryInputs aligned ram

end Airbender.Blake2G.Call
