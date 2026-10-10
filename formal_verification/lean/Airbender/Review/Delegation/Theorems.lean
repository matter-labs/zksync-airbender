import Airbender.Proofs.Delegation.Memory
import Airbender.Proofs.Delegation.Operations

namespace Airbender.Delegation

/-- All four families can share one initialized memory pool. Imported writes
    preserve canonical RV32 words, and logical matching supplies every later
    read. `inputs` lists modeled tables and the remaining caller/padding rules;
    no family restriction, read-value or limb-range premise is supplied. -/
theorem operation_memory_soundness [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : MemoryAccepted data) (inputs : OperationInputs data before cells control) :
    MemorySoundness data ∧ WordBounds data :=
  ⟨Proofs.memory_soundness (by norm_num [Trace.timestampBase]; omega) accepted inputs.publicState,
    Proofs.operation_word_bounds hp inverse accepted inputs⟩

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
