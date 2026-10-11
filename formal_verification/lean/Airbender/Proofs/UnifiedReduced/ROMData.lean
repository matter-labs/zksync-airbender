import Airbender.Proofs.UnifiedReduced.ROMTransfers
import Airbender.Review.UnifiedReduced.NativeROM
import Airbender.Proofs.UnifiedReduced.History

namespace Airbender.UnifiedReduced.ROMView
open Trace Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

def data [Fact p.Prime] (before : State) (native : UnifiedTrace p) : UnifiedTrace p :=
  { native with rows := native.rows.map (row before)
                initialMemory := native.initialMemory.map (Trace.ROMView.token before)
                terminalMemory := native.terminalMemory.map (Trace.ROMView.token before) }

theorem accepted [Fact p.Prime] (hp : 131072 < p)
    (before : State) {trace : UnifiedTrace p} (native : Accepted trace) : Accepted (data before trace) := by
  have transfers : ∀ r ∈ trace.rows,
      (row before r).reads = r.reads.map (Trace.ROMView.token before) ∧
      (row before r).writes = r.writes.map (Trace.ROMView.token before) := by
    intro r member
    exact row_transfers hp before r trace.rom (native.active r member) (native.constraints r member)
  constructor
  · intro r member
    change r ∈ trace.rows.map (row before) at member
    obtain ⟨original, inRows, rfl⟩ := List.mem_map.mp member
    exact row_holds (by omega) before original trace.rom
      (native.active original inRows) (native.constraints original inRows)
  · intro r member
    change r ∈ trace.rows.map (row before) at member
    obtain ⟨original, inRows, rfl⟩ := List.mem_map.mp member
    have active := native.active original inRows
    unfold row
    split <;> simpa [Row.columns, CircuitLayout.columns, importedConstraintsTraceColumns, readData] using active
  · simpa [data, List.map_map, Function.comp_def] using native.states
  · have matching := native.memory.map (Trace.ROMView.token before)
    have reads : (trace.rows.map (row before)).flatMap Row.reads =
        (trace.rows.flatMap Row.reads).map (Trace.ROMView.token before) := by
      simp only [List.flatMap_map, List.map_flatMap]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro r member
      exact (transfers r member).1
    have writes : (trace.rows.map (row before)).flatMap Row.writes =
        (trace.rows.flatMap Row.writes).map (Trace.ROMView.token before) := by
      simp only [List.flatMap_map, List.map_flatMap]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro r member
      exact (transfers r member).2
    simpa only [data, reads, writes, List.map_append] using matching

theorem decoded [Fact p.Prime] (before : State)
    {trace : UnifiedTrace p} {program : List ProgramEntry} (native : Decoded trace program) :
    Decoded (data before trace) program := by
  intro r member
  change r ∈ trace.rows.map (row before) at member
  obtain ⟨original, inRows, rfl⟩ := List.mem_map.mp member
  simpa using native original inRows

theorem boot_inputs [Fact p.Prime] (hp : 4 < p)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (inputs : BootInputsWith projection trace initial cells program) :
    NativeInputs projection (data initial trace) initial cells program := by
  obtain ⟨image, publicImage⟩ := inputs.image
  have seedImage := Trace.ROMView.seed_image inputs.profile publicImage
  have clocks := Trace.ROMView.native_clocks hp inputs.seed inputs.initialPC
  constructor
  · exact inputs.distinct
  · exact inputs.aligned
  · change initialImage initial cells = some (trace.initialMemory.map (Trace.ROMView.token initial))
    rw [inputs.seed, seedImage]
    exact publicImage
  · refine ⟨⟨4, 0⟩, ?_⟩
    change initialState initial (4, 0) = some trace.initial
    rw [inputs.initialPC]
    simp [initialState, inputs.profile.pc, PCState.boundary]
  · exact inputs.programImage
  · refine ⟨clocks.initial, clocks.aligned, ?_⟩
    intro lifted member
    change lifted ∈ trace.initialMemory.map (Trace.ROMView.token initial) at member
    obtain ⟨native, present, rfl⟩ := List.mem_map.mp member
    simpa only [Trace.ROMView.token_time] using clocks.memory native present

theorem memory_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (native : Accepted trace) (inputs : BootInputs trace initial cells program)
    (membership : Decoded trace program) : MemoryExecution (data initial trace) initial cells :=
  Proofs.memory_execution hp inverse
    (accepted (by dsimp [timestampBase] at hp; omega) initial native)
    (boot_inputs (by dsimp [timestampBase] at hp; omega) inputs)
    (decoded initial membership)

end Airbender.UnifiedReduced.ROMView
