import Airbender.Proofs.UnifiedReduced.MixedHistory
import Airbender.Proofs.UnifiedReduced.CustomComposition
import Airbender.Proofs.UnifiedReduced.RowExecution
import Airbender.Proofs.Trace.PositionComposition

namespace Airbender.UnifiedReduced.Mixed.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem custom_no_standard_clause [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {entry : ProgramEntry} (fields : customDecoderFields entry.instruction = some entry.data) :
    instructionClause entry.instruction = none := by
  obtain arithmetic | rotation := UnifiedReduced.Proofs.custom_instruction_cases fields
  · obtain ⟨rs1, rs2, rd, encoding⟩ := arithmetic
    rw [encoding]; rfl
  · obtain ⟨kind, rs1, rd, encoding⟩ := rotation
    rw [encoding]; fin_cases kind <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem row_clause [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (accepted : Accepted trace) (inputs : Mixed.Inputs trace initial cells program)
    (memory : MemoryExecution (ROMView.data initial trace) initial cells)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ (ROMView.data initial trace).rows)
    {before after : State}
    (position : RowPosition (ROMView.data initial trace) initial cells ⟨.machine, w⟩
      (retiredState before (Control.initialPC w).toBitVec))
    {entry : ProgramEntry} (present : entry ∈ program)
    (source : entry.SourceWith initial Mixed.decoderFields) (query : decoderQuery w = entry.query)
    (history : SailHistory cells
      (rowEvents (ROMView.data initial trace).memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ clause, Mixed.clauseFor entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  rcases fields_cases source.fields with standard | custom
  · have epoch : (ROMView.data initial trace).memoryEpoch = trace.memoryEpoch := by
      simp only [Data.memoryEpoch, ROMView.data, List.map_map, Function.comp_def, Trace.ROMView.token_address]
    have nativeHistory := epoch ▸ history
    obtain ⟨clause, selected, execution⟩ := UnifiedReduced.Proofs.row_clause_from_memory hp inverse byteInverse
      accepted inputs memory member position present ⟨source.bytes, source.decoded, standard⟩ query nativeHistory
    exact ⟨clause, by simp [Mixed.clauseFor, selected], execution⟩
  · have physical := ROMView.accepted (by omega) initial accepted
    have nativeInputs := ROMView.boot_inputs (by omega) inputs.boot
    obtain ⟨clause, selected, execution⟩ := UnifiedReduced.Proofs.custom_row_clause_from_memory
      (by dsimp [timestampBase]; omega) inverse byteInverse physical nativeInputs inputs.boot.setup memory
      member position custom query history
    exact ⟨clause, by simp [Mixed.clauseFor, custom_no_standard_clause custom, selected], execution⟩

set_option backward.isDefEq.respectTransparency false in
theorem row_step [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (accepted : Accepted trace) (decoded : Decoded trace program)
    (inputs : Mixed.Inputs trace initial cells program)
    (memory : MemoryExecution (ROMView.data initial trace) initial cells)
    {row : Row p UnifiedFamily} (member : row ∈ (ROMView.data initial trace).rows)
    {before after : State} {events : List MemoryAccess}
    (position : RowPosition (ROMView.data initial trace) initial cells row (retiredState before row.start.word.toBitVec))
    (native : ∀ event ∈ events, event ∈ (ROMView.data initial trace).nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents (ROMView.data initial trace).memoryEpoch row).reverse before after) :
    Mixed.Step program (retiredState before row.start.word.toBitVec) (retiredState after row.finish.word.toBitVec) := by
  have physical := ROMView.accepted (by omega) initial accepted
  have physicalDecoded := ROMView.decoded initial decoded
  obtain ⟨addresses, image⟩ := inputs.boot.programImage
  obtain ⟨entry, present, family, query⟩ := decoder_member (physicalDecoded row member)
  have original := run_program_sources image entry present
  have source := source_after_history (by omega) physical past native original (inputs.code entry present)
  have fetched := native_query_pc_word (by dsimp [limbBase]; omega) query
  change row.start.word = Word.ofBitVec entry.pc at fetched
  have pc : row.start.word.toBitVec = entry.pc := by rw [fetched, Word.ofBitVec_roundtrip]
  refine ⟨entry, present, entry_source_retired_state source _, ?_, ?_⟩
  · simpa only [pc] using retired_state_pc before row.start.word.toBitVec
  · cases row with
    | mk kind w =>
      cases kind
      exact row_clause hp inverse byteInverse accepted inputs memory member position present original query history

set_option backward.isDefEq.respectTransparency false in
theorem trace_execution [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (inputs : Mixed.Inputs trace initial cells program)
    (accepted : Accepted trace) (decoded : Decoded trace program) :
    Realizes (Mixed.Step program) trace initial cells (Trace.ROMView.token initial) := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  let physical := ROMView.data initial trace
  have constraints := ROMView.accepted (by omega) initial accepted
  have publicInputs := ROMView.boot_inputs (by omega) inputs.boot
  obtain ⟨timestamp, initialBound⟩ := publicInputs.initialPC
  have initialRead := initial_state_pc (by dsimp [limbBase]; omega) initialBound
  have memory := memory_execution clockSize inverse constraints publicInputs (ROMView.decoded initial decoded)
  obtain ⟨history, rows, nativeAfter, consistent, permutation, ordered, nativeHistory, matchedState⟩ :=
    memory_execution clockSize inverse constraints publicInputs (ROMView.decoded initial decoded)
  have chain := ordered_row_boundaries clockSize inverse constraints publicInputs.clocks permutation ordered
  have eventPermutation :
      (rows.flatMap fun row => (rowEvents physical.memoryEpoch row).reverse).Perm physical.nativeEvents := by
    rw [native_events_projection clockSize inverse constraints publicInputs.clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have execution := compose_native_rows_at initialRead
    (fun row member {before after events} position native past current =>
      row_step hp inverse byteInverse accepted decoded inputs memory member position native past current)
    rows [] physical.terminal permutation ordered
    (fun event present => eventPermutation.mem_iff.mp present) chain nativeHistory
  obtain ⟨final, execution, pc, values⟩ := native_trace_postconditions clockSize inverse constraints
    publicInputs.clocks publicInputs.image publicInputs.distinct initialRead consistent chain nativeHistory matchedState execution
  refine ⟨final, execution, pc, ?_⟩
  intro sink member
  obtain ⟨cell, present, address, read⟩ := values (Trace.ROMView.token initial sink)
    (List.mem_map.mpr ⟨sink, member, rfl⟩)
  exact ⟨cell, present, (Trace.ROMView.token_address initial sink).symm ▸ address, read⟩

end Airbender.UnifiedReduced.Mixed.Proofs
