import Airbender.Proofs.Keccak.ReferenceCalls

namespace Airbender.Keccak.Call
open Trace Reference.RiscV.Sail

/-- The existing initialized 649-call public span executes complete independent
    reference micro-calls in actual Sail states. Its schedule derives supported
    controls; initialized matching derives canonical lanes and pointer ABI.
    Mixed caller fetch/PC retirement and participation remain separate claims. -/
theorem execution_soundness [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {initial : State} {domain : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : NativeCallInputs data initial domain)
    (tables : data.setup = Delegation.modeledSetup Controller.rows)
    (aligned : ∀ cell ∈ domain, cell.Aligned)
    (ram : ∀ address, Cell.ram address ∈ domain → ROM.limit ≤ address.toNat) :
    ∃ after, Relation.ReflTransGen Executes initial after ∧ Delegation.TraceMapping data initial after domain := by
  have clockBound : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  exact Proofs.span_reference hp inverse accepted
    (inputs.toBoundaryInputs clockBound accepted) tables aligned ram

end Airbender.Keccak.Call
