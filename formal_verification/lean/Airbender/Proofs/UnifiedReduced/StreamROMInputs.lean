import Airbender.Proofs.UnifiedReduced.StreamROMCallerCycles
import Airbender.Proofs.UnifiedReduced.StreamNativePrefix
import Airbender.Proofs.UnifiedReduced.StreamInitialization

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail
open Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- Native boot supplies bounded seed timestamps without a physical value image. -/
theorem native_seed_clocks {data : RequestTrace babyBearModulus}
    {initial : State} {cells : List Cell} {program : List UnifiedReduced.ProgramEntry}
    (boot : BootInputsWith Stream.decoderFields data.machine initial cells program) :
    ∀ token ∈ data.machine.initialMemory, (timeOfPair token.time).Bounded := by
  intro token member
  rw [boot.seed] at member
  obtain ⟨cell, _, rfl⟩ := List.mem_map.mp member
  simp [Cell.initialToken, timeOfPair, Timestamp.Bounded, timestampBase]

/-- Native boot and caller source produce physical stream inputs after ROM interpretation. -/
theorem interpreted_inputs
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {cells : List Cell}
    (boot : BootInputsWith Stream.decoderFields data.machine initial cells program)
    (callers : ∃ addresses, programImage initial addresses = some data.program)
    (tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows) :
    ∃ ca oa, NativeMemoryInputsWith Stream.decoderFields
      (NativeROM.view initial data) program initial ca oa cells := by
  obtain ⟨ca, callerImage⟩ := callers
  obtain ⟨oa, ordinaryImage⟩ := boot.programImage
  obtain ⟨image, physical⟩ := boot.image
  have seed := Trace.ROMView.seed_image boot.profile physical
  have clocks := Trace.ROMView.native_clocks (by decide) boot.seed boot.initialPC
  refine ⟨ca, oa, ⟨?_, clocks.initial, clocks.aligned⟩, ordinaryImage, ?_, ?_,
    boot.aligned, boot.setup, tables⟩
  · exact callerImage
  · change initialImage initial cells = some (data.machine.initialMemory.map (Trace.ROMView.token initial))
    rw [boot.seed, seed]
    exact physical
  · exact boot.distinct.map cell_address_injective

/-- Every interpreted row retains its original accepted native equation witness. -/
theorem interpreted_raw_rows {data : RequestTrace babyBearModulus}
    {program : List UnifiedReduced.ProgramEntry} {initial : State}
    (accepted : MixedMemoryAccepted data program)
    (setup : data.machine.rom = Setup.table initial) :
    ∀ w, (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈
      (NativeROM.view initial data).machine.rows →
      ∃ raw, FlatOperation.ConstraintsHoldFlat (Verification.environment raw)
        (importedConstraints (Setup.table initial)) ∧ raw 4 = 1 ∧
        w = (ROMView.row initial (⟨.machine, raw⟩ : Trace.Row babyBearModulus UnifiedFamily)).assignment := by
  intro w member
  obtain ⟨⟨kind, raw⟩, present, equal⟩ := List.mem_map.mp member
  cases kind
  have core := Verification.holds_of_sublist (accepted.constraints _ present)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  rw [setup] at core
  refine ⟨raw, core, accepted.active _ present, ?_⟩
  exact (congrArg Trace.Row.assignment equal).symm

/-- ROM interpretation keeps the external selector and destination response. -/
theorem interpreted_stream_row (initial : State) (row : Trace.Row p UnifiedFamily) :
    Stream.isRead (ROMView.row initial row) = Stream.isRead row ∧
      Stream.response (ROMView.row initial row) = Stream.response row ∧
      (ROMView.row initial row).clock = row.clock := by
  rcases row with ⟨kind, w⟩
  cases kind
  unfold ROMView.row
  split <;> constructor
  all_goals first | rfl | exact ⟨rfl, rfl⟩

/-- ROM interpretation consumes the same number of external words. -/
theorem interpreted_read_count [Fact p.Prime] (initial : State) (data : RequestTrace p) :
    Stream.readCount (NativeROM.view initial data).machine = Stream.readCount data.machine := by
  simp only [Stream.readCount, ExternalStream.count, NativeROM.view, ROMView.data, List.filter_map,
    Function.comp_def, (interpreted_stream_row initial _).1, List.length_map]

/-- ROM interpretation retains each clock-ordered external response binding. -/
theorem interpreted_stream_ports [Fact p.Prime] (initial : State) {data : RequestTrace p}
    {stream : List (BitVec 32)} (ports : Stream.StreamPorts data.machine stream) :
    Stream.StreamPorts (NativeROM.view initial data).machine stream := by
  intro row member selected
  obtain ⟨native, present, rfl⟩ := List.mem_map.mp member
  have facts := interpreted_stream_row initial native
  have source := ports native present (facts.1 ▸ selected)
  simpa only [ExternalStream.index, NativeROM.view, ROMView.data, List.filter_map,
    Function.comp_def, (interpreted_stream_row initial _).1,
    (interpreted_stream_row initial _).2.2, List.length_map, facts.2.1] using source

/-- Physical execution returns the target's original native terminal interface. -/
theorem interpreted_realizes [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {cells : List Cell} {stream : List (BitVec 32)}
    (execution : Stream.Realizes stream program data.program
      (NativeROM.view initial data).machine initial cells) :
    Stream.Realizes stream program data.program data.machine initial cells (Trace.ROMView.token initial) := by
  obtain ⟨after, steps, pc, terminal⟩ := execution
  refine ⟨after, ?_, pc, ?_⟩
  · simpa only [interpreted_read_count] using steps
  · intro token member
    obtain ⟨cell, included, address, read⟩ := terminal _ (List.mem_map.mpr ⟨token, member, rfl⟩)
    exact ⟨cell, included, by simpa only [Trace.ROMView.token_address] using address, read⟩

end Airbender.UnifiedReduced.Caller.Stream.Proofs
