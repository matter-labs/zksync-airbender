import Airbender.Proofs.UnifiedReduced.RowExecution
import Airbender.Proofs.UnifiedReduced.Code
import Airbender.Proofs.Trace.PositionComposition

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false in
theorem row_step [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (accepted : Accepted trace) (decoded : Decoded trace program)
    (inputs : ExecutionInputs trace initial cells program)
    {row : Row p UnifiedFamily} (member : row ∈ (ROMView.data initial trace).rows)
    {before after : State} {events : List MemoryAccess}
    (position : RowPosition (ROMView.data initial trace) initial cells row (retiredState before row.start.word.toBitVec))
    (native : ∀ event ∈ events, event ∈ (ROMView.data initial trace).nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents (ROMView.data initial trace).memoryEpoch row).reverse before after) :
    Step program (retiredState before row.start.word.toBitVec) (retiredState after row.finish.word.toBitVec) := by
  have physical := ROMView.accepted (by omega) initial accepted
  have physicalDecoded := ROMView.decoded initial decoded
  have nativeInputs := ROMView.boot_inputs (by omega) inputs.boot
  obtain ⟨addresses, image⟩ := nativeInputs.programImage
  obtain ⟨entry, present, family, query⟩ := decoder_member (physicalDecoded row member)
  have originalSource := run_program_sources image entry present
  have source := source_after_history (by omega) physical past native originalSource (inputs.code entry present)
  have fetched := native_query_pc_word (by dsimp [limbBase]; omega) query
  change row.start.word = Word.ofBitVec entry.pc at fetched
  have pc : row.start.word.toBitVec = entry.pc := by rw [fetched, Word.ofBitVec_roundtrip]
  refine ⟨entry, present, entry_source_retired_state source _, ?_, ?_⟩
  · simpa only [pc] using retired_state_pc before row.start.word.toBitVec
  · cases row with
    | mk kind w =>
      cases kind
      have epoch : (ROMView.data initial trace).memoryEpoch = trace.memoryEpoch := by
        simp only [Data.memoryEpoch, ROMView.data, List.map_map, Function.comp_def, Trace.ROMView.token_address]
      rw [epoch] at history
      exact row_clause hp inverse byteInverse accepted decoded inputs member position present query history

set_option backward.isDefEq.respectTransparency false in
theorem trace_execution [Fact p.Prime] [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (inputs : ExecutionInputs trace initial cells program)
    (accepted : Accepted trace) (decoded : Decoded trace program) :
    Realizes (Step program) trace initial cells (Trace.ROMView.token initial) := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  let physical := ROMView.data initial trace
  have constraints := ROMView.accepted (by omega) initial accepted
  have publicInputs := ROMView.boot_inputs (by omega) inputs.boot
  obtain ⟨timestamp, initialBound⟩ := publicInputs.initialPC
  have initialRead := initial_state_pc limbSize initialBound
  obtain ⟨history, rows, nativeAfter, consistent, permutation, ordered, nativeHistory, matchedState⟩ :=
    ROMView.memory_execution clockSize inverse accepted inputs.boot decoded
  have chain := ordered_row_boundaries clockSize inverse constraints publicInputs.clocks permutation ordered
  have eventPermutation :
      (rows.flatMap fun row => (rowEvents physical.memoryEpoch row).reverse).Perm physical.nativeEvents := by
    rw [native_events_projection clockSize inverse constraints publicInputs.clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have execution := compose_native_rows_at initialRead
    (fun row member {before after events} position native past current =>
      row_step hp inverse byteInverse accepted decoded inputs member position native past current)
    rows [] physical.terminal permutation ordered
    (fun event present => eventPermutation.mem_iff.mp present) chain nativeHistory
  obtain ⟨final, execution, pc, values⟩ := native_trace_postconditions clockSize inverse constraints
    publicInputs.clocks publicInputs.image publicInputs.distinct initialRead consistent chain nativeHistory matchedState execution
  refine ⟨final, execution, pc, ?_⟩
  intro sink member
  obtain ⟨cell, present, address, read⟩ := values (Trace.ROMView.token initial sink)
    (List.mem_map.mpr ⟨sink, member, rfl⟩)
  exact ⟨cell, present, (Trace.ROMView.token_address initial sink).symm ▸ address, read⟩

end Airbender.UnifiedReduced.Proofs
