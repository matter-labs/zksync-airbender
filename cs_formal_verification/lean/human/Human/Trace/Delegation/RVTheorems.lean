module
public import Human.Helpers.Delegation.RVOperations
public import Human.Trace.Delegation.RVExecution

@[expose] public section

-- The statements proven in slop/Slop/Final/Trace/Delegation/RVTheorems.lean (checked by verify.sh). The
-- public starting point is an `RV.State` (`RVMemoryInputs`); execution is `RVMemoryExecution` (RV cell reads/writes).

namespace Airbender.Delegation

/-- Initialized native matching realizes all delegation reads/writes in
    actual RV registers and RAM, ending at the declared terminal values. RAM cells are RAM at every address,
    INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`): no pointer is required
    to be at or above `ROM_END`. `aligned` is physical word alignment of the public cell domain. No read, result or
    range premise is supplied. -/
def RVNativeMemoryExecutionClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p) {data : MemoryData p} (accepted : MemoryAccepted data) {before : RV.State} {cells : List Trace.Cell} (inputs : RVMemoryInputs data before cells) (aligned : ∀ cell ∈ cells, cell.Aligned),
    RVMemoryExecution data before cells

/-- All four families can share one pool initialized from an
    `RV.State`. Imported writes preserve canonical RV32 words, and logical matching supplies every later read. No
    family restriction, read-value or limb-range premise is supplied. -/
def RVOperationMemorySoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p) (inverse : 64 * (-31457280 : ZMod p) = 1) {data : MemoryData p} {before : RV.State} {cells : List Trace.Cell} {control : Fin 4096 → Vector Nat 6} (accepted : MemoryAccepted data) (inputs : RVOperationInputs data before cells control),
    MemorySoundness data ∧ WordBounds data

/-- Imported delegation constraints and initialized token matching imply native
    clock/address bounds, strict per-cell order and Clean memory consistency. The public inputs are the RV
    initialization (`initialImageRV`), a distinct cell domain and native timestamp-offset room. No prior-clock,
    read-value or address-range premise. -/
def RVMemorySoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (hp : 2 * Trace.timestampBase + 4 < p) {data : MemoryData p} (accepted : MemoryAccepted data) {before : RV.State} {cells : List Trace.Cell} (inputs : RVMemoryInputs data before cells),
    MemorySoundness data

end Airbender.Delegation
