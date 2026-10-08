import Airbender.Proofs.Trace.OfflineMemory
import Airbender.Proofs.Trace.Values
import Airbender.Proofs.Trace.PC
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

theorem latest_reads {trace : Data babyBearModulus}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, LatestRead trace row port :=
  Proofs.latest_reads (by decide) (by decide) accepted boundary unique

/-- Every initialized address has a Clean online-consistent history containing
    all its native accesses, including an explicit initial-value write. -/
theorem cell_histories {trace : Data babyBearModulus}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    ∀ source ∈ trace.initialMemory, ∃ history, CellHistory trace source history :=
  Proofs.native_cell_histories (by decide) (by decide) accepted boundary unique

/-- Initial word bounds and program-table ranges propagate through the native
    history to every operand read. No bound on an individual read is assumed. -/
theorem read_bounds {trace : Data babyBearModulus}
    (accepted : Accepted trace) (clocks : ClockBoundary trace) (values : ValueBoundary trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded :=
  Proofs.read_bounds (by decide) (by decide) accepted clocks values

theorem terminal_bounds {trace : Data babyBearModulus}
    (accepted : Accepted trace) (clocks : ClockBoundary trace) (values : ValueBoundary trace) :
    ∀ token ∈ trace.terminalMemory, token.word.Bounded :=
  Proofs.terminal_bounds (by decide) (by decide) accepted clocks values

/-- A readable, distinct public Sail address domain supplies bounded native
    initialization cells with bounded zero clocks and no duplicate address. -/
theorem initial_image_conditions {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImage before cells = some tokens)
    (domain : cells.Nodup) :
    (∀ token ∈ tokens, token.word.Bounded) ∧
      (∀ token ∈ tokens, (timeOfPair token.time).Bounded) ∧
      (tokens.map MemoryToken.address).Nodup :=
  ⟨Proofs.image_bounds image, Proofs.image_clocks image, Proofs.image_unique image domain⟩

/-- The initial PC comes from Sail; native matching and imported output queries
    then bound every row PC and the terminal PC. -/
theorem pc_bounds {trace : Data babyBearModulus} {before : Reference.RiscV.Sail.State}
    {timestamp : ZMod babyBearModulus × ZMod babyBearModulus}
    (accepted : Accepted trace) (initial : initialState before timestamp = some trace.initial) :
    (∀ row ∈ trace.rows, row.start.word.Bounded ∧ row.finish.word.Bounded) ∧
      trace.terminal.word.Bounded :=
  Proofs.trace_pc_bounds accepted (Proofs.initial_pc_bound (by decide) initial)

end Airbender.Trace
