import Airbender.Proofs.Reduced.ROMAcceptance
import Airbender.Proofs.Reduced.TargetInputs

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail Delegation.Caller
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- The reduced filter retains the original stream decoder metadata. -/
theorem reduced_fields_original {instruction : SailRV32.instruction}
    {data : DecoderData PooledFamily}
    (selected : Caller.reducedDecoderFields instruction = some data) :
    External.decoderFields instruction = some data := by
  cases fields : External.decoderFields instruction with
  | none => simp [Caller.reducedDecoderFields, fields] at selected
  | some raw =>
    have metadata : raw = data ∧ Caller.reducedFamily data.family = true := by
      simpa [Caller.reducedDecoderFields, fields] using selected
    exact congrArg some metadata.1

/-- Use the same public entries in the complete stream decoder registry. -/
theorem full_projection_boot [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] [Fact p.Prime]
    {data : PooledTrace p} {program : List PooledProgramEntry} {initial : State} {cells : List Cell}
    (boot : PooledBootInputs data initial cells program Caller.reducedDecoderFields) :
    PooledBootInputs data initial cells program External.decoderFields := by
  refine { boot with programImage := ?_ }
  obtain ⟨addresses, image⟩ := boot.programImage
  refine ⟨program.map ProgramEntry.pc, ?_⟩
  apply Airbender.Compiler.PublicProgram.image_run
  intro entry member
  have source := run_program_sources image entry member
  exact ⟨source.bytes, source.decoded, reduced_fields_original source.fields⟩

/-- Native zero seeds have canonical timestamps independently of their values. -/
theorem native_seed_clocks [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] [Fact p.Prime]
    {data : PooledTrace p} {program : List PooledProgramEntry} {initial : State} {cells : List Cell}
    (boot : PooledBootInputs data initial cells program Caller.reducedDecoderFields) :
    ∀ token ∈ data.initialMemory, (timeOfPair token.time).Bounded := by
  intro token member
  rw [boot.seed] at member
  obtain ⟨cell, _, rfl⟩ := List.mem_map.mp member
  simp [Cell.initialToken, timeOfPair, Timestamp.Bounded, timestampBase]

/-- ROM interpretation constructs the physical public inputs for the shared path. -/
theorem interpreted_inputs [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    [Fact p.Prime] (hp : FieldCapacity.NoWrap p 4)
    {data : RequestTrace p} {program : List PooledProgramEntry} {initial : State} {cells : List Cell}
    (boot : PooledBootInputs data.machine initial cells program Caller.reducedDecoderFields)
    (callers : ∃ addresses, Delegation.Caller.programImage initial addresses = some data.program)
    (tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows) :
    ∃ ca oa, StreamMemoryInputs (NativeROM.view initial data) program initial ca oa cells := by
  have physical := PooledROMView.execution_boundary hp (full_projection_boot boot)
  obtain ⟨ca, callerImage⟩ := callers
  obtain ⟨oa, ordinaryImage⟩ := physical.programImage
  have clocks := ROMView.native_clocks hp boot.seed boot.initialBoundary
  refine ⟨ca, oa, ⟨?_, physical.image, ?_, boot.aligned⟩,
    ordinaryImage, physical.wordSetup, physical.subwordSetup, tables⟩
  · exact ⟨callerImage, clocks.initial, clocks.aligned⟩
  · exact boot.distinct.map cell_address_injective

/-- ROM interpretation preserves native read selection and its clock. -/
theorem interpreted_stream_row [Fact p.Prime] (initial : State) (row : Trace.Row p PooledFamily) :
    External.isRead (PooledROMView.row initial row) = External.isRead row ∧
      (PooledROMView.row initial row).clock = row.clock := by
  constructor
  · rcases row with ⟨family, w⟩
    cases family <;> first | rfl | (dsimp only [PooledROMView.row]; split <;> rfl)
  · change (timeOfPair (PooledROMView.row initial row).start.timestamp).value =
      (timeOfPair row.start.timestamp).value
    rw [PooledROMView.row_start]

/-- ROM interpretation consumes the same independent input words. -/
theorem interpreted_read_count [Fact p.Prime] (initial : State) (data : RequestTrace p) :
    External.readCount (NativeROM.view initial data).machine = External.readCount data.machine := by
  simp only [External.readCount, NonDeterminism.Pooled.readCount, ExternalStream.count,
    NativeROM.view, PooledROMView.data, List.filter_map, Function.comp_def,
    (interpreted_stream_row initial _).1, List.length_map]

/-- Each selected external response keeps its original clock-ordered binding. -/
theorem interpreted_stream_ports [Fact p.Prime] (initial : State) {data : RequestTrace p}
    {stream : List (BitVec 32)} (ports : External.StreamPorts data.machine stream) :
    External.StreamPorts (NativeROM.view initial data).machine stream := by
  intro row member selected
  obtain ⟨native, present, rfl⟩ := List.mem_map.mp member
  have facts := interpreted_stream_row initial native
  have active : External.isRead native = true := facts.1 ▸ selected
  have unchanged : PooledROMView.row initial native = native := by
    rcases native with ⟨family, w⟩
    cases family <;> first | rfl | simp [External.isRead, NonDeterminism.Pooled.isRead] at active
  have source := ports native present active
  simpa only [ExternalStream.index, NativeROM.view, PooledROMView.data, List.filter_map,
    Function.comp_def, (interpreted_stream_row initial _).1,
    (interpreted_stream_row initial _).2, List.length_map, unchanged] using source

/-- Return the unchanged native terminal interface after physical execution. -/
theorem interpreted_realizes [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] [Fact p.Prime]
    {data : RequestTrace p} {program : List PooledProgramEntry}
    {initial : State} {cells : List Cell} {stream : List (BitVec 32)}
    (execution : Caller.ReducedRealizes stream program data.program
      (NativeROM.view initial data).machine initial cells) :
    Caller.ReducedRealizes stream program data.program data.machine initial cells (ROMView.token initial) := by
  obtain ⟨after, steps, pc, terminal⟩ := execution
  refine ⟨after, ?_, pc, ?_⟩
  · simpa only [interpreted_read_count] using steps
  · intro token member
    obtain ⟨cell, included, address, read⟩ := terminal _ (List.mem_map.mpr ⟨token, member, rfl⟩)
    exact ⟨cell, included, by simpa only [ROMView.token_address] using address, read⟩

end Airbender.AddSub.Modular.External.Caller.Proofs
