import Human.Helpers.Delegation.Operations
import Human.Trace.Delegation.Execution

-- The statements proven in slop/Slop/Final/Trace/Delegation/Theorems.lean (checked by verify.sh).

namespace Airbender.Delegation

/-- Initialized native matching realizes all delegation reads/writes in actual
    Sail registers and RAM, ending at the declared terminal values. `aligned`
    is physical word alignment of the public cell domain. No read, result or
    range premise is supplied; modeled table conditions are only needed for
    the additional operation/word-bound claims below. -/
def NativeMemoryExecutionClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p) {data : MemoryData p} (accepted : MemoryAccepted data) {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell} (inputs : MemoryInputs data before cells) (aligned : ∀ cell ∈ cells, cell.Aligned),
    MemoryExecution data before cells

/-- All four families can share one initialized memory pool. Imported writes
    preserve canonical RV32 words, and logical matching supplies every later
    read. `inputs` lists modeled tables and the remaining caller/padding rules;
    no family restriction, read-value or limb-range premise is supplied. -/
def OperationMemorySoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (inverse : 64 * (-31457280 : ZMod p) = 1) {data : MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell} {control : Fin 4096 → Vector Nat 6} (accepted : MemoryAccepted data) (inputs : OperationInputs data before cells control),
    MemorySoundness data ∧ WordBounds data

/-- Imported delegation constraints and initialized token matching imply native
    clock/address bounds, strict per-cell order and Clean memory consistency.
    The public inputs are actual Sail initialization, a distinct cell domain and
    native timestamp-offset room. No prior-clock, read-value or address-range premise. -/
def MemorySoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p) {data : MemoryData p} (accepted : MemoryAccepted data) {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell} (inputs : MemoryInputs data before cells),
    MemorySoundness data

end Airbender.Delegation
