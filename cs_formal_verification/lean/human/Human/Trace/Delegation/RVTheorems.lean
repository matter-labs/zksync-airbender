module
public import Human.Helpers.Delegation.RVOperations
public import Human.Trace.Delegation.RVExecution
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

-- The statements proven in proven/Proven/Final/Trace/Delegation/RVTheorems.lean (checked by verify.sh). The
-- public starting point is an `RV.State` (`RVMemoryInputs`); execution is `RVMemoryExecution` (RV cell reads/writes).

namespace Airbender.Delegation

/-- Initialized native matching realizes all delegation reads/writes in
    actual RV registers and RAM, ending at the declared terminal values. RAM cells are RAM at every address,
    INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`): no pointer is required
    to be at or above `ROM_END`. `aligned` is physical word alignment of the public cell domain. No read, result or
    range premise is supplied. -/
def RVNativeMemoryExecutionClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 2 * Trace.timestampBase + 4 < p) {data : MemoryData p} (_accepted : MemoryAccepted data) {before : RV.State} {cells : List Trace.Cell} (_inputs : RVMemoryInputs data before cells) (_aligned : ∀ cell ∈ cells, cell.Aligned),
    RVMemoryExecution data before cells

/-- All four families can share one pool initialized from an
    `RV.State`. Imported writes preserve canonical RV32 words, and logical matching supplies every later read. No
    family restriction, read-value or limb-range premise is supplied. -/
def RVOperationMemorySoundnessClaim : Prop :=
  ∀ {data : MemoryData babyBearModulus} {before : RV.State} {cells : List Trace.Cell} {control : Fin 4096 → Vector Nat 6} (_accepted : MemoryAccepted data) (_inputs : RVOperationInputs data before cells control),
    MemorySoundness data ∧ WordBounds data

/-- Imported delegation constraints and initialized token matching imply native
    clock/address bounds, strict per-cell order and Clean memory consistency. The public inputs are the RV
    initialization (`initialImageRV`), a distinct cell domain and native timestamp-offset room. No prior-clock,
    read-value or address-range premise. -/
def RVMemorySoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime] (_hp : 2 * Trace.timestampBase + 4 < p) {data : MemoryData p} (_accepted : MemoryAccepted data) {before : RV.State} {cells : List Trace.Cell} (_inputs : RVMemoryInputs data before cells),
    MemorySoundness data

/-- The assumptions of `RVNativeMemoryExecutionClaim` can be met (at BabyBear) by a pool with a row. -/
def RVNativeMemoryExecutionSatisfiableClaim : Prop :=
  ∃ (data : MemoryData babyBearModulus) (before : RV.State) (cells : List Trace.Cell),
    2 * Trace.timestampBase + 4 < babyBearModulus ∧ MemoryAccepted data ∧ RVMemoryInputs data before cells ∧
      (∀ cell ∈ cells, cell.Aligned) ∧ data.rows ≠ []

/-- The assumptions of `RVOperationMemorySoundnessClaim` can be met by a pool with a row. -/
def RVOperationMemorySoundnessSatisfiableClaim : Prop :=
  ∃ (data : MemoryData babyBearModulus) (before : RV.State) (cells : List Trace.Cell)
    (control : Fin 4096 → Vector Nat 6),
    MemoryAccepted data ∧ RVOperationInputs data before cells control ∧ data.rows ≠ []

/-- The assumptions of `RVMemorySoundnessClaim` can be met (at BabyBear) by a pool with a row. -/
def RVMemorySoundnessSatisfiableClaim : Prop :=
  ∃ (data : MemoryData babyBearModulus) (before : RV.State) (cells : List Trace.Cell),
    2 * Trace.timestampBase + 4 < babyBearModulus ∧ MemoryAccepted data ∧ RVMemoryInputs data before cells ∧
      data.rows ≠ []

end Airbender.Delegation
