import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Delegation.Requests
import Airbender.Proofs.Delegation.Memory
import Airbender.Proofs.Delegation.Operations
import Airbender.Proofs.Delegation.Terminal
import Airbender.Review.Trace.Delegation.Execution

namespace Airbender.Delegation

/-- Initialized native matching realizes all delegation reads/writes in actual
    Sail registers and RAM, ending at the declared terminal values. `aligned`
    is physical word alignment of the public cell domain. Read values and results
    are derived; MemoryInputs retains clockRoom and invocationHigh bounds.
    Modeled table conditions are only needed for
    the additional operation/word-bound claims below. -/
theorem native_memory_execution [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (inputs : MemoryInputs data before cells) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    MemoryExecution data before cells :=
  Proofs.native_memory_execution hp accepted inputs.toBoundaryInputs aligned

/-- All four families can share one initialized memory pool. Imported writes
    preserve canonical RV32 words, and logical matching supplies every later
    read. `inputs` lists modeled tables and the remaining caller/padding rules;
    no family restriction, read-value or data-limb-range premise is supplied.
    The memory inputs retain clockRoom and invocationHigh. -/
theorem operation_memory_soundness [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Scale64 p)
    {data : MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : MemoryAccepted data) (inputs : OperationInputs data before cells control) :
    MemorySoundness data ∧ WordBounds data :=
  ⟨Proofs.memory_soundness (by norm_num [Trace.timestampBase]; omega) accepted inputs.publicState.toBoundaryInputs,
    Proofs.operation_word_bounds hp inverse accepted inputs⟩

/-- Imported delegation constraints and initialized token matching imply native
    clock/address bounds, strict per-cell order and Clean memory consistency.
    The public inputs are actual Sail initialization, a distinct cell domain and
    native timestamp-offset room. No prior-clock, read-value or address-range premise. -/
theorem memory_soundness [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p Trace.timestampBase)
    {data : MemoryData p} (accepted : MemoryAccepted data)
    {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (inputs : MemoryInputs data before cells) : MemorySoundness data :=
  Proofs.memory_soundness hp accepted inputs.toBoundaryInputs

end Airbender.Delegation
