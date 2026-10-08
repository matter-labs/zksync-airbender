import Airbender.Proofs.Trace.OfflineMemory
import Airbender.Proofs.Trace.Values
import Airbender.Proofs.Trace.PC
import Airbender.Proofs.Trace.Program
import Airbender.Proofs.Trace.Addresses
import Airbender.Proofs.Trace.ROM
import Airbender.Proofs.Trace.MemoryHistory
import Airbender.Proofs.Trace.Composition
import Airbender.Proofs.Trace.Initialization
import Airbender.Proofs.Trace.ROMView
import Airbender.Proofs.Trace.NonDeterminism
import Airbender.Proofs.BabyBear

namespace Airbender.Trace

/-- Construct the physical Sail memory view at PC=0/time=4. For native
    zero-valued ROM permutation slots, use `NativeBootBoundary` below. -/
theorem boot_boundary {trace : Data babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (profile : InitialProfile before cells)
    (image : bootImage before cells = some trace.initialMemory)
    (initial : trace.initial = PCState.boundary 0 (4, 0)) :
    initialImage before cells = some trace.initialMemory ∧
      initialState before (4, 0) = some trace.initial ∧ ClockBoundary trace :=
  Proofs.boot_boundary (by decide) profile image initial

/-- The modeled ROM setup obtains its value ranges and disabled-query behavior
    from the public Sail memory image. -/
theorem rom_value_boundary {trace : Data babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory) : ValueBoundary trace :=
  ROM.Proofs.value_boundary (by decide) image setup

/-- Every active modeled ROM query returns its public Sail bytes. This uniform
    binding mentions no selected circuit row or expected execution result. -/
theorem rom_reads {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {tokens : List (MemoryToken babyBearModulus)}
    (image : initialImage before cells = some tokens) : ROM.Reads before (ROM.table cells tokens) :=
  ROM.Proofs.read (by decide) image

/-- Every native address is an actual cell of the public Sail image. Register
    indices and RAM address limbs therefore inherit their canonical bounds. -/
theorem initialized_cells {trace : Data babyBearModulus}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      ∃ cell ∈ cells, port.address.code row.assignment = cell.addressCode :=
  Proofs.initialized_cells (by decide) (by decide) accepted boundary image

theorem address_bounds {trace : Data babyBearModulus}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (port.address.word row.assignment).Bounded :=
  Proofs.address_bounds (by decide) (by decide) accepted boundary image

/-- Native decoder membership identifies actual public bytes and their original
    Sail instruction at every row's PC. No decoded-instruction premise is used. -/
theorem decoder_soundness {trace : Data babyBearModulus}
    (accepted : Accepted trace)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List ProgramEntry}
    (image : programImage before addresses = some program) (decoded : Decoded trace program) :
    ∀ row ∈ trace.rows, row.Fetched before :=
  Proofs.decoder_soundness (by decide) accepted image decoded

/-- The original Sail decoder also binds the custom nondeterminism CSR's
    native metadata. This extends fetch/selector coverage, not the seven-
    instruction execution theorem; stream consumption is a separate claim. -/
theorem NonDeterminism.decoder_soundness {trace : Data babyBearModulus}
    (accepted : Accepted trace)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List ProgramEntry}
    (image : programImageWith NonDeterminism.decoderFields before addresses = some program)
    (decoded : Decoded trace program) :
    ∀ row ∈ trace.rows, row.Fetched before NonDeterminism.decoderFields :=
  NonDeterminism.Proofs.decoder_soundness (by decide) accepted image decoded

theorem decoder_immediate_bounds {trace : Data babyBearModulus}
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List ProgramEntry}
    (image : programImage before addresses = some program) (decoded : Decoded trace program) :
    ∀ row ∈ trace.rows, row.decoderImmediate.Bounded :=
  Proofs.decoder_immediate_bounds (by decide) image decoded

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

/-- All native register/RAM accesses compose into one Clean online-consistent
    history, including explicit initialization of nonzero public values. -/
theorem memory_history {trace : Data babyBearModulus}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    ∃ history, MemoryHistory trace history :=
  Proofs.native_memory_history (by decide) (by decide) accepted boundary unique

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

/-- Every accepted selected trace has an actual Sail execution from its public
    initial state to the native terminal PC and register/RAM values. The
    public boundary supplies initial data; `loads` explicitly excludes the
    unresolved LW-to-x0 memory access. -/
theorem sail_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {trace : Data babyBearModulus} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List ProgramEntry}
    (inputs : ExecutionBoundary trace before cells program)
    (loads : NoDiscardedLoads program)
    (accepted : Accepted trace) (decoded : Decoded trace program) :
    ∃ after, SailTrace program before after ∧
      Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) after =
        .ok trace.terminal.word.toBitVec after ∧
      ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok (Proofs.memoryWord sink.value) after :=
  Proofs.restricted_trace_execution .sail (by decide) (by decide) inputs (fun _ => loads) accepted decoded

/-- The same whole-trace claim for the documented Airbender instruction
    profile, including LW-to-x0. That case uses Sail's NOP clause; other
    instructions use their unchanged Sail clauses. Public initial data and
    logical matching/membership remain explicit in `inputs`/`accepted`/`decoded`. -/
theorem airbender_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {trace : Data babyBearModulus} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List ProgramEntry}
    (inputs : ExecutionBoundary trace before cells program)
    (accepted : Accepted trace) (decoded : Decoded trace program) :
    ∃ after, AirbenderTrace program before after ∧
      Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) after =
        .ok trace.terminal.word.toBitVec after ∧
      ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok (Proofs.memoryWord sink.value) after :=
  Proofs.restricted_trace_execution .airbender (by decide) (by decide) inputs
    (by intro impossible; cases impossible) accepted decoded

/-- Native zero-initialized ADD/ADDI/SUB/LUI/AUIPC + LW/SW execution. Native
    ROM slots stay separate from public code/data bytes. Registers and RAM
    terminal values are exact; ROM bytes are the readonly public image. The
    proof reuses the same imported constraints and existing Sail trace claim. -/
theorem native_boot_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {trace : Data babyBearModulus} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List ProgramEntry}
    (inputs : NativeBootBoundary trace before cells program)
    (accepted : Accepted trace) (decoded : Decoded trace program) :
    ∃ after, AirbenderTrace program before after ∧
      Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) after =
        .ok trace.terminal.word.toBitVec after ∧
      ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok (Proofs.memoryWord (ROMView.token before sink).value) after := by
  have clocks := ROMView.native_clocks (by decide) inputs.seed inputs.initial
  obtain ⟨after, execution, pc, terminal⟩ := airbender_soundness
    (ROMView.execution_boundary (by decide) inputs)
    (ROMView.accepted (by decide) (by decide) before accepted clocks inputs.seed)
    (ROMView.decoded before decoded)
  refine ⟨after, execution, pc, ?_⟩
  intro sink member
  have lifted := terminal (ROMView.token before sink) (List.mem_map_of_mem member)
  simpa only [ROMView.token_address] using lifted

end Airbender.Trace
