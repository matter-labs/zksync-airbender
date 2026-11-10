module
public import Human.Helpers.Core.BabyBearPrime
public import Human.Helpers.Context.Registries.Pooled
public import Human.Helpers.UnifiedReduced.Registry
public import Human.Helpers.Delegation.Memory
public import Human.Circuits.KeccakSplit.Native

@[expose] public section

/-! No row of a formalised circuit writes a memory-argument token at timestamp 0.

    In Airbender, initial memory values (all RAM, including the ROM shadow, starts at zero) enter the memory
    argument only through the init circuits, which write at timestamp 0. These claims show that no row of the
    circuits formalised here (the six pooled CPU families, the unified reduced machine, the four delegation
    workers and the split Keccak workers) writes at timestamp 0, so none of them can masquerade as an initial
    value. The init circuits themselves (zero value, timestamp 0) are `InitsTeardowns.StandaloneClaim` and
    `InitsTeardowns.UnifiedClaim`, from which the boot claims derive that the tracked RAM starts at zero
    (`Trace.BootRamZeroClaim`, `UnifiedReduced.BootRamZeroClaim`). What remains unformalised: the cross-chunk clock
    chaining.
    The statements mention no machine state. Proven in slop/Slop/Final/Trace/ZeroTimestamp.lean. -/

namespace Airbender.Trace

/-- Every write token of an accepted six-family pooled trace that boots at native clock four (the boot premise
    `RVPooledBootInputs.initialBoundary`) has clock at least four: each row writes at its start clock plus a port
    offset, and state matching chains every row start back to the initial clock. -/
def NoZeroTimestampWritesClaim : Prop :=
  ∀ {trace : PooledTrace babyBearModulus} (_accepted : Accepted trace)
    (_boot : trace.initial = PCState.boundary 0 (4, 0)),
    ∀ row ∈ trace.rows, ∀ token ∈ row.writes, 4 ≤ (timeOfPair token.time).value

end Airbender.Trace

namespace Airbender.UnifiedReduced
open Trace

/-- The same for the unified reduced machine, booting at native clock four (`BootInputsWith.initialPC`). -/
def NoZeroTimestampWritesClaim : Prop :=
  ∀ {trace : UnifiedTrace babyBearModulus} (_accepted : Accepted trace)
    (_boot : trace.initial = PCState.boundary 0 (4, 0)),
    ∀ row ∈ trace.rows, ∀ token ∈ row.writes, 4 ≤ (timeOfPair token.time).value

end Airbender.UnifiedReduced

namespace Airbender.Delegation
open Trace

/-- Every write of a delegation row (bigint, Blake2s G, Blake2s round, Keccak) has clock at least two: it is the
    invocation clock plus the port offset two. `clockRoom` and `invocationHigh` are the clock fields of
    `RVMemoryInputs`; no acceptance is needed. -/
def NoZeroTimestampWritesClaim : Prop :=
  ∀ {data : MemoryData babyBearModulus}
    (_clockRoom : ∀ row ∈ data.rows,
      (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase)
    (_invocationHigh : ∀ row ∈ data.rows,
      (decodeTimestamp row.assignment row.columns.invocation).hi < timestampBase),
    ∀ row ∈ data.rows, ∀ port ∈ row.ports, 2 ≤ (timeOfPair (row.writeToken port).time).value

end Airbender.Delegation

namespace Airbender.Keccak.Split.Native
open Trace

/-- The same for the split Keccak workers (`RVMemoryInputs.clockRoom`, `RVMemoryInputs.invocationHigh`). -/
def NoZeroTimestampWritesClaim : Prop :=
  ∀ {data : MemoryData babyBearModulus}
    (_clockRoom : ∀ row ∈ data.rows,
      (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase)
    (_invocationHigh : ∀ row ∈ data.rows,
      (decodeTimestamp row.assignment row.columns.invocation).hi < timestampBase),
    ∀ row ∈ data.rows, ∀ port ∈ row.ports, 2 ≤ (timeOfPair (row.writeToken port).time).value

end Airbender.Keccak.Split.Native
