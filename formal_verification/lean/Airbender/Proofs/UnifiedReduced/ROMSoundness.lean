import Airbender.Proofs.UnifiedReduced.ROMData
import Airbender.Review.Circuits.UnifiedReduced.WordROM
import Airbender.Proofs.UnifiedReduced.WordMemorySoundness
import Airbender.Proofs.UnifiedReduced.ROMCopy

namespace Airbender.UnifiedReduced.WordMemory.NativeROM.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem soundness_from_memory [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (boot : BootInputsWith projection trace initial cells program)
    (accepted : Accepted trace) (memory : MemoryExecution (ROMView.data initial trace) initial cells)
    {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output} {w : Nat → ZMod p}
    (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ (ROMView.data initial trace).rows)
    (words : UnifiedReduced.WordMemory.WordMapping input output w)
    (position : RowPosition (ROMView.data initial trace) initial cells ⟨.machine, w⟩ input.before)
    {entry : ProgramEntry} (source : entry.SourceWith initial decoderFields)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
      else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4))
    (configuration : FlatMemoryConfiguration initial)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (destination : input.store = false → input.rd ≠ zeroRegister) :
    Airbender.WordMemory.spec input output := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have physical := ROMView.accepted (by omega) initial accepted
  have nativeInputs := ROMView.boot_inputs (by omega) boot
  have fields := WordMemory.Proofs.decoded_metadata source.fields encoding destination
  change (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows.map (ROMView.row initial) at member
  obtain ⟨native, inRows, equal⟩ := List.mem_map.mp member
  have assignment : w = (ROMView.row initial native).assignment := congrArg Row.assignment equal.symm
  have originalQuery : decoderQuery native.assignment = entry.query := by
    have rowQuery := congrArg Row.decoderQuery equal
    rw [ROMView.row_query] at rowQuery
    simpa [← query, decoderQuery, Row.decoderQuery, CircuitLayout.decoderColumns,
      CircuitLayout.columns, Row.columns, Row.decoderColumns, importedConstraintsDecoderColumns,
      importedConstraintsTraceColumns] using rowQuery
  have core := Verification.holds_of_sublist (accepted.constraints _ inRows)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  have core : FlatOperation.ConstraintsHoldFlat (Verification.environment native.assignment)
      (importedConstraints (Setup.table initial)) := by
    cases native.family
    simpa [Row.constraints, CircuitLayout.constraints, clockConstraints, boot.setup] using core
  have flags := UnifiedReduced.Proofs.decoder_selectors (by omega) core
    (UnifiedReduced.Proofs.decoder_field_bounds source.fields).2.1 originalQuery
  have load : native.assignment 28 = if input.store then 0 else 1 := by
    have bit := flags 17
    rw [fields] at bit
    cases mode : input.store <;> simpa [WordMemory.Proofs.metadata, mode,
      importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using bit
  have store : native.assignment 29 = if input.store then 1 else 0 := by
    have bit := flags 18
    rw [fields] at bit
    cases mode : input.store <;> simpa [WordMemory.Proofs.metadata, mode,
      importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using bit
  have active : native.assignment 4 = 1 := by
    simpa [Row.columns, CircuitLayout.columns, importedConstraintsTraceColumns]
      using accepted.active native inRows
  have copy := ROMView.row_word_copy hp input.store core active load store
  have nativeEqual : (⟨.machine, native.assignment⟩ : Row p UnifiedFamily) = native := by cases native; rfl
  rw [nativeEqual] at copy
  have copied : output.data.toBitVec = input.readData.toBitVec := by
    have dataWord : output.data = Word.mk (w 50).val (w 51).val :=
      congrArg₂ Word.mk words.dataLo words.dataHi
    have readWord : input.readData = Word.mk (w 42).val (w 43).val :=
      congrArg₂ Word.mk words.readLo words.readHi
    simpa only [dataWord, readWord, assignment] using copy
  apply WordMemory.Proofs.row_soundness_from_memory clockSize inverse physical
    (List.mem_map.mpr ⟨native, inRows, equal⟩) words position source query encoding memory nativeInputs
    configuration ordinary destination copied

theorem soundness [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : UnifiedTrace p) (initial : State) (cells : List Cell) (program : List ProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) Airbender.WordMemory.spec := by
  rintro input output w ⟨assumptions, ⟨accepted, decoded, member⟩, mapping⟩
  obtain ⟨addresses, image⟩ := assumptions.boot.programImage
  obtain ⟨entry, present, query, encoding⟩ := mapping.instruction
  exact soundness_from_memory hp inverse assumptions.boot accepted
    (ROMView.memory_execution (by dsimp [timestampBase]; omega) inverse accepted assumptions.boot decoded)
    member mapping.words mapping.state (run_program_sources image entry present) query encoding
    assumptions.configuration assumptions.ordinary assumptions.destination

end Airbender.UnifiedReduced.WordMemory.NativeROM.Proofs
