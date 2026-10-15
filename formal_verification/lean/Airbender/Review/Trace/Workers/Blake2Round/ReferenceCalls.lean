import Airbender.Proofs.Blake2Round.ReferenceCalls

namespace Airbender.Blake2Round.Call
open Trace Reference.RiscV.Sail

/-- The existing seven or ten round public span executes complete independent
    reference micro-calls in the actual full Sail states, with exact writes and
    frame. Initialized control history derives the exclusive round, all mode
    flags and pointer ABI. Mixed caller fetch/PC retirement and total worker
    participation remain separate composition claims. -/
theorem execution_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {domain : List Cell} {flags : Fin 8}
    (accepted : Delegation.MemoryAccepted data) (inputs : NativeCallInputs data initial domain flags)
    (aligned : ∀ cell ∈ domain, cell.Aligned)
    (ram : ∀ address, Cell.ram address ∈ domain → ROM.limit ≤ address.toNat) :
    ∃ after, Relation.ReflTransGen Executes initial after ∧ Delegation.TraceMapping data initial after domain :=
  Proofs.span_reference hp inverse accepted inputs.toBoundaryInputs aligned ram

end Airbender.Blake2Round.Call
