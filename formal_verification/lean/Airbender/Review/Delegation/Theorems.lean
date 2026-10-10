import Airbender.Proofs.Delegation.Memory

namespace Airbender.Delegation

/-- Imported delegation constraints and initialized token matching imply native
    clock/address bounds, strict per-cell order and Clean memory consistency.
    The public inputs are actual Sail initialization, a distinct cell domain and
    caller-clock alignment. No prior-clock, read-value or address-range premise. -/
theorem memory_soundness [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (inputs : MemoryInputs data before cells) : MemorySoundness data :=
  Proofs.memory_soundness hp accepted inputs

end Airbender.Delegation
