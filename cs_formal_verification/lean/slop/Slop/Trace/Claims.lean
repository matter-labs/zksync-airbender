import Slop.Final.Trace.Families.AddSub.Theorems
import Slop.Final.Trace.Soundness
import Slop.Trace.OfflineMemory
import Slop.Trace.Values
import Slop.Trace.PC
import Slop.Trace.Program
import Slop.Trace.Addresses
import Slop.Trace.ROM
import Slop.Trace.MemoryHistory
import Slop.Trace.Composition
import Slop.Trace.Initialization
import Slop.Trace.ROMView
import Slop.Trace.NonDeterminism
import Slop.Trace.OracleConsumption
import Slop.Trace.OracleComposition
import Slop.Trace.PooledOracleConsumption
import Slop.Trace.PooledOracleDecoder
import Slop.BabyBear
import Slop.Trace.PooledComposition

namespace Airbender.Trace


theorem pooled_sail_soundness
    {trace : PooledTrace babyBearModulus} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List PooledProgramEntry}
    (inputs : PooledInputs trace before cells program)
    (accepted : Accepted trace) (decoded : PooledDecoded trace program) :
    Realizes (PooledStep program) trace before cells :=
  Proofs.pooled_trace_execution (by decide) (by decide) inputs accepted decoded


theorem boot_boundary {trace : Data babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (profile : InitialProfile before cells)
    (image : bootImage before cells = some trace.initialMemory)
    (initial : trace.initial = PCState.boundary 0 (4, 0)) :
    initialImage before cells = some trace.initialMemory ∧
      initialState before (4, 0) = some trace.initial ∧ ClockBoundary trace :=
  Proofs.boot_boundary (by decide) profile image initial


theorem rom_value_boundary {trace : Data babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (image : initialImage before cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory) : ValueBoundary trace :=
  ROM.Proofs.value_boundary (by decide) image setup


theorem rom_reads {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {tokens : List (MemoryToken babyBearModulus)}
    (image : initialImage before cells = some tokens) : ROM.Reads before (ROM.table cells tokens) :=
  ROM.Proofs.read (by decide) image


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


theorem decoder_soundness {trace : Data babyBearModulus}
    (accepted : Accepted trace)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List ProgramEntry}
    (image : programImage before addresses = some program) (decoded : Decoded trace program) :
    ∀ row ∈ trace.rows, row.Fetched before :=
  Proofs.decoder_soundness (by decide) accepted image decoded


theorem NonDeterminism.decoder_soundness {trace : Data babyBearModulus}
    (accepted : Accepted trace)
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List ProgramEntry}
    (image : programImageWith NonDeterminism.decoderFields before addresses = some program)
    (decoded : Decoded trace program) :
    ∀ row ∈ trace.rows, row.Fetched before NonDeterminism.decoderFields :=
  NonDeterminism.Proofs.decoder_soundness (by decide) accepted image decoded


theorem NonDeterminism.native_consumption {trace : Data babyBearModulus}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {stream : List (BitVec 32)} (ports : NonDeterminism.StreamPorts trace stream) :
    ∃ rows, rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      ∃ rest, stream = NonDeterminism.consumed rows ++ rest :=
  NonDeterminism.Proofs.native_consumption (by decide) (by decide) accepted clocks ports


theorem NonDeterminism.Pooled.native_consumption {trace : PooledTrace babyBearModulus}
    (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {stream : List (BitVec 32)} (ports : NonDeterminism.Pooled.StreamPorts trace stream) :
    ∃ rows, rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      ∃ rest, stream = NonDeterminism.Pooled.consumed rows ++ rest :=
  NonDeterminism.Pooled.Proofs.native_consumption (by decide) (by decide) accepted clocks ports


theorem NonDeterminism.Pooled.decoder_soundness {trace : PooledTrace babyBearModulus}
    (accepted : Accepted trace) {before : Reference.RiscV.Sail.State}
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (image : NonDeterminism.Pooled.programImage before addresses = some program)
    (decoded : PooledDecoded trace program) :
    ∀ row ∈ trace.rows, NonDeterminism.Pooled.Fetched row before :=
  NonDeterminism.Pooled.Proofs.decoder_soundness (by decide) accepted image decoded


theorem decoder_immediate_bounds {trace : Data babyBearModulus}
    {before : Reference.RiscV.Sail.State} {addresses : List (BitVec 32)}
    {program : List ProgramEntry}
    (image : programImage before addresses = some program) (decoded : Decoded trace program) :
    ∀ row ∈ trace.rows, row.decoderImmediate.Bounded :=
  Proofs.decoder_immediate_bounds (by decide) image decoded


theorem clocks {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    ∀ row ∈ trace.rows, ClockEffects row.columns row.assignment :=
  Proofs.trace_clocks (by decide) (by decide) accepted boundary


theorem terminal_clock {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    (timeOfPair trace.terminal.timestamp).value =
      (timeOfPair trace.initial.timestamp).value + 4 * trace.rows.length :=
  Proofs.trace_terminal_clock (by decide) (by decide) accepted boundary


theorem state_path {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    ∃ path, StatePath trace path :=
  Proofs.native_state_path (by decide) (by decide) accepted boundary


theorem unique_access_times {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) : trace.accessTimes.Nodup :=
  Proofs.access_times_unique (by decide) (by decide) accepted boundary


theorem initialized_addresses {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      port.address.code row.assignment ∈ trace.initialMemory.map MemoryToken.address :=
  Proofs.initialized_addresses (by decide) (by decide) accepted boundary


theorem memory_paths {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    ∀ source ∈ trace.initialMemory, ∃ path, MemoryPath trace source path :=
  Proofs.native_memory_paths (by decide) (by decide) accepted boundary unique


theorem latest_reads {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, LatestRead trace row port :=
  Proofs.latest_reads (by decide) (by decide) accepted boundary unique


theorem cell_histories {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    ∀ source ∈ trace.initialMemory, ∃ history, CellHistory trace source history :=
  Proofs.native_cell_histories (by decide) (by decide) accepted boundary unique


theorem memory_history {Kind : Type} [CircuitLayout Kind] [Proofs.ClockLaws Kind babyBearModulus]
    {trace : Data babyBearModulus Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    ∃ history, MemoryHistory trace history :=
  Proofs.native_memory_history (by decide) (by decide) accepted boundary unique


theorem read_bounds {trace : Data babyBearModulus}
    (accepted : Accepted trace) (clocks : ClockBoundary trace) (values : ValueBoundary trace) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded :=
  Proofs.read_bounds (by decide) (by decide) accepted clocks values


theorem terminal_bounds {trace : Data babyBearModulus}
    (accepted : Accepted trace) (clocks : ClockBoundary trace) (values : ValueBoundary trace) :
    ∀ token ∈ trace.terminalMemory, token.word.Bounded :=
  Proofs.terminal_bounds (by decide) (by decide) accepted clocks values


theorem initial_image_conditions {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImage before cells = some tokens)
    (domain : cells.Nodup) :
    (∀ token ∈ tokens, token.word.Bounded) ∧
      (∀ token ∈ tokens, (timeOfPair token.time).Bounded) ∧
      (tokens.map MemoryToken.address).Nodup :=
  ⟨Proofs.image_bounds image, Proofs.image_clocks image, Proofs.image_unique image domain⟩


theorem pc_bounds {trace : Data babyBearModulus} {before : Reference.RiscV.Sail.State}
    {timestamp : ZMod babyBearModulus × ZMod babyBearModulus}
    (accepted : Accepted trace) (initial : initialState before timestamp = some trace.initial) :
    (∀ row ∈ trace.rows, row.start.word.Bounded ∧ row.finish.word.Bounded) ∧
      trace.terminal.word.Bounded :=
  Proofs.trace_pc_bounds accepted (Proofs.initial_pc_bound (by decide) initial)


theorem NonDeterminism.soundness
    {trace : Data babyBearModulus} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List ProgramEntry}
    (inputs : ExecutionBoundary trace before cells program NonDeterminism.decoderFields)
    (accepted : Accepted trace) (decoded : Decoded trace program)
    {stream : List (BitVec 32)} (ports : NonDeterminism.StreamPorts trace stream) :
    ∃ after, NonDeterminism.ExecutionTrace stream program (before, 0)
        (after, NonDeterminism.readCount trace) ∧
      Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) after =
        .ok trace.terminal.word.toBitVec after ∧
      ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok (memoryWord sink.value) after :=
  NonDeterminism.Proofs.trace_execution (by decide) (by decide) inputs accepted decoded ports


theorem NonDeterminism.native_boot_soundness
    {trace : Data babyBearModulus} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {program : List ProgramEntry}
    (inputs : NativeBootBoundary trace before cells program NonDeterminism.decoderFields)
    (accepted : Accepted trace) (decoded : Decoded trace program)
    {stream : List (BitVec 32)} (ports : NonDeterminism.StreamPorts trace stream) :
    ∃ after, NonDeterminism.ExecutionTrace stream program (before, 0)
        (after, NonDeterminism.readCount trace) ∧
      Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) after =
        .ok trace.terminal.word.toBitVec after ∧
      ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok (memoryWord (ROMView.token before sink).value) after := by
  have clocks := ROMView.native_clocks (by decide) inputs.seed inputs.initial
  obtain ⟨after, execution, pc, terminal⟩ := NonDeterminism.soundness
    (ROMView.execution_boundary (by decide) inputs)
    (ROMView.accepted (by decide) (by decide) before accepted clocks inputs.seed)
    (ROMView.decoded before decoded) (NonDeterminism.Proofs.view_stream_ports before ports)
  rw [NonDeterminism.Proofs.view_read_count] at execution
  refine ⟨after, execution, pc, ?_⟩
  intro sink member
  have lifted := terminal (ROMView.token before sink) (List.mem_map_of_mem member)
  simpa only [ROMView.token_address, id_eq] using lifted

end Airbender.Trace
