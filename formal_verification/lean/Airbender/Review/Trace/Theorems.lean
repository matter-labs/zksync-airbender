import Airbender.Proofs.Trace.MemoryOrigins
import Airbender.Proofs.Trace.MemoryPaths
import Airbender.Proofs.BabyBear

namespace Airbender.Trace

/-- Every selected row advances by four ticks, and its native accesses follow
    their previous writes. Only initial clock conditions remain; the per-row
    clock interfaces are derived from the logical native matching relations. -/
theorem clocks {trace : Data babyBearModulus}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    ∀ row ∈ trace.rows, ClockEffects row.columns row.assignment :=
  Proofs.trace_clocks (by decide) (by decide) accepted boundary

theorem terminal_clock {trace : Data babyBearModulus}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    (timeOfPair trace.terminal.timestamp).value =
      (timeOfPair trace.initial.timestamp).value + 4 * trace.rows.length :=
  Proofs.trace_terminal_clock (by decide) (by decide) accepted boundary

/-- The matched native rows form one complete state path; its clock values are
    distinct. No row ordering or absence of disconnected cycles is assumed. -/
theorem state_path {trace : Data babyBearModulus}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    ∃ path, StatePath trace path :=
  Proofs.native_state_path (by decide) (by decide) accepted boundary

theorem unique_access_times {trace : Data babyBearModulus}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) : trace.accessTimes.Nodup :=
  Proofs.access_times_unique (by decide) (by decide) accepted boundary

theorem initialized_addresses {trace : Data babyBearModulus}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      port.address.code row.assignment ∈ trace.initialMemory.map MemoryToken.address :=
  Proofs.initialized_addresses (by decide) (by decide) accepted boundary

/-- Native accesses form a complete ordered history for each initialized cell.
    The initial image supplies one cell per address; expected reads are derived. -/
theorem memory_paths {trace : Data babyBearModulus}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    ∀ source ∈ trace.initialMemory, ∃ path, MemoryPath trace source path :=
  Proofs.native_memory_paths (by decide) (by decide) accepted boundary unique

end Airbender.Trace
