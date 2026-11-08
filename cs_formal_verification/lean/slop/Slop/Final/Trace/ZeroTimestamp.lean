module
public import Human.Trace.ZeroTimestamp
public import Slop.Trace.ZeroTimestamp
public import Slop.Trace.Pooled
public import Slop.UnifiedReduced.Trace
public import Slop.Delegation.Memory
public import Slop.KeccakSplit.Memory.History

@[expose] public section

/-! The no-zero-timestamp-write claims of `Human.Trace.ZeroTimestamp`. -/

namespace Airbender.Trace

/-- Every write token of an accepted six-family pooled trace that boots at native clock four has clock at least
    four: each row writes at its start clock plus a port offset, and state matching chains every row start back to
    the initial clock. -/
theorem no_zero_timestamp_writes {trace : PooledTrace babyBearModulus} (accepted : Accepted trace)
    (boot : trace.initial = PCState.boundary 0 (4, 0)) :
    ∀ row ∈ trace.rows, ∀ token ∈ row.writes, 4 ≤ (timeOfPair token.time).value :=
  Proofs.boot_writes_after_four (by decide) (by decide) accepted boot

end Airbender.Trace

namespace Airbender.UnifiedReduced
open Trace

/-- The same for the unified reduced machine, booting at native clock four (`BootInputsWith.initialPC`). -/
theorem no_zero_timestamp_writes {trace : UnifiedTrace babyBearModulus} (accepted : Accepted trace)
    (boot : trace.initial = PCState.boundary 0 (4, 0)) :
    ∀ row ∈ trace.rows, ∀ token ∈ row.writes, 4 ≤ (timeOfPair token.time).value :=
  Trace.Proofs.boot_writes_after_four (by decide) (by decide) accepted boot

end Airbender.UnifiedReduced

namespace Airbender.Delegation
open Trace

/-- Every write of a delegation row (bigint, Blake2s G, Blake2s round, Keccak) has clock at least two: it is the
    invocation clock plus the port offset two. `clockRoom` and `invocationHigh` are the clock fields of
    `MemoryInputs`; no acceptance is needed. -/
theorem no_zero_timestamp_writes {data : MemoryData babyBearModulus}
    (clockRoom : ∀ row ∈ data.rows,
      (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase)
    (invocationHigh : ∀ row ∈ data.rows,
      (decodeTimestamp row.assignment row.columns.invocation).hi < timestampBase) :
    ∀ row ∈ data.rows, ∀ port ∈ row.ports, 2 ≤ (timeOfPair (row.writeToken port).time).value := by
  intro row member port present
  have offset := Proofs.port_offset row present
  have after : port.clock.offset ≤ (timeOfPair (row.writeToken port).time).value :=
    Trace.Proofs.invocation_write_after (by decide) (by rw [offset]; exact clockRoom row member)
      (invocationHigh row member)
  omega

end Airbender.Delegation

namespace Airbender.Keccak.Split.Native
open Trace

/-- The same for the split Keccak workers (`MemoryInputs.clockRoom`, `MemoryInputs.invocationHigh`). -/
theorem no_zero_timestamp_writes {data : MemoryData babyBearModulus}
    (clockRoom : ∀ row ∈ data.rows,
      (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase)
    (invocationHigh : ∀ row ∈ data.rows,
      (decodeTimestamp row.assignment row.columns.invocation).hi < timestampBase) :
    ∀ row ∈ data.rows, ∀ port ∈ row.ports, 2 ≤ (timeOfPair (row.writeToken port).time).value := by
  intro row member port present
  have offset := Proofs.port_offset row present
  have after : port.clock.offset ≤ (timeOfPair (row.writeToken port).time).value :=
    Trace.Proofs.invocation_write_after (by decide) (by rw [offset]; exact clockRoom row member)
      (invocationHigh row member)
  omega

end Airbender.Keccak.Split.Native
