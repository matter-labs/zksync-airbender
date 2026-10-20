import Slop.UnifiedReduced.CustomCases
import Slop.UnifiedReduced.TriAddNative
import Slop.UnifiedReduced.XorRotateExecution
import Slop.Trace.PositionComposition

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

set_option backward.isDefEq.respectTransparency false in
theorem custom_row_clause_from_memory [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (accepted : Accepted trace)
    (inputs : NativeInputs projection trace initial cells program)
    (setup : trace.rom = Setup.table initial) (memory : MemoryExecution trace initial cells)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    {before after : State}
    (position : RowPosition trace initial cells ⟨.machine, w⟩
      (retiredState before (Control.initialPC w).toBitVec))
    {entry : ProgramEntry} (fields : customDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ clause, Custom.clauseFor entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  obtain arithmetic | rotation := custom_instruction_cases fields
  · obtain ⟨rs1, rs2, rd, encoding⟩ := arithmetic
    let input : TriAdd.Input := ⟨TriAdd.leftOperand w, TriAdd.rightOperand w, TriAdd.oldDestination w,
      rs1, rs2, rd, Control.initialPC w, retiredState before (Control.initialPC w).toBitVec⟩
    have words : TriAdd.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w := by
      constructor <;> rfl
    refine ⟨TriAdd.execution input, ?_, ?_⟩
    · rw [encoding]
      rfl
    · exact triadd_execution_from_memory hp clockInverse accepted inputs member words rfl position
        fields memory query encoding history
  · obtain ⟨kind, rs1, rd, encoding⟩ := rotation
    let input : XorRotate.Input := ⟨kind, TriAdd.leftOperand w, TriAdd.rightOperand w,
      rs1, rd, Control.initialPC w, retiredState before (Control.initialPC w).toBitVec⟩
    have words : XorRotate.WordMapping input ⟨Control.destination w, Control.finalPC w⟩ w := by
      constructor <;> rfl
    refine ⟨XorRotate.execution input, ?_, ?_⟩
    · rw [encoding]
      fin_cases kind <;> rfl
    · exact xorrot_execution_from_memory hp clockInverse byteInverse accepted inputs setup member
        words rfl position fields memory query encoding history

set_option backward.isDefEq.respectTransparency false in
theorem custom_row_clause [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (accepted : Accepted trace) (decoded : Decoded trace program)
    (inputs : Custom.Inputs trace initial cells program)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    {before after : State}
    (position : RowPosition trace initial cells ⟨.machine, w⟩
      (retiredState before (Control.initialPC w).toBitVec))
    {entry : ProgramEntry} (present : entry ∈ program) (query : decoderQuery w = entry.query)
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ clause, Custom.clauseFor entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  obtain ⟨addresses, image⟩ := inputs.initialization.programImage
  exact custom_row_clause_from_memory hp clockInverse byteInverse accepted inputs.initialization inputs.setup
    (custom_memory_execution hp clockInverse accepted inputs.initialization decoded)
    member position (run_program_sources image entry present).fields query history

set_option backward.isDefEq.respectTransparency false in
theorem custom_row_step [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (accepted : Accepted trace) (decoded : Decoded trace program)
    (inputs : Custom.Inputs trace initial cells program)
    {row : Row p UnifiedFamily} (member : row ∈ trace.rows)
    {before after : State} {events : List MemoryAccess}
    (position : RowPosition trace initial cells row (retiredState before row.start.word.toBitVec))
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after) :
    Custom.Step program (retiredState before row.start.word.toBitVec) (retiredState after row.finish.word.toBitVec) := by
  obtain ⟨addresses, image⟩ := inputs.initialization.programImage
  obtain ⟨entry, present, family, query⟩ := decoder_member (decoded row member)
  have original := run_program_sources image entry present
  have source := entry_source_after_history past
    (fun event present pc inside address => native_rom_unchanged (by dsimp [timestampBase] at hp; omega)
      accepted (native event present) pc inside address) original (inputs.code entry present).1 (inputs.code entry present).2
  have fetched := native_query_pc_word (by dsimp [limbBase, timestampBase] at *; omega) query
  change row.start.word = Word.ofBitVec entry.pc at fetched
  have pc : row.start.word.toBitVec = entry.pc := by rw [fetched, Word.ofBitVec_roundtrip]
  refine ⟨entry, present, entry_source_retired_state source _, ?_, ?_⟩
  · simpa only [pc] using retired_state_pc before row.start.word.toBitVec
  · cases row with
    | mk kind w =>
      cases kind
      exact custom_row_clause hp clockInverse byteInverse accepted decoded inputs member position present query history

set_option backward.isDefEq.respectTransparency false in
theorem custom_trace_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (inputs : Custom.Inputs trace initial cells program)
    (accepted : Accepted trace) (decoded : Decoded trace program) :
    Realizes (Custom.Step program) trace initial cells := by
  obtain ⟨timestamp, initialBound⟩ := inputs.initialization.initialPC
  have initialRead := initial_state_pc (by dsimp [limbBase, timestampBase] at hp ⊢; omega) initialBound
  obtain ⟨history, rows, nativeAfter, consistent, permutation, ordered, nativeHistory, matchedState⟩ :=
    custom_memory_execution hp clockInverse accepted inputs.initialization decoded
  have chain := ordered_row_boundaries hp clockInverse accepted inputs.initialization.clocks permutation ordered
  have eventPermutation :
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
    rw [native_events_projection hp clockInverse accepted inputs.initialization.clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have execution := compose_native_rows_at initialRead
    (fun row member {before after events} position native past current =>
      custom_row_step hp clockInverse byteInverse accepted decoded inputs member position native past current)
    rows [] trace.terminal permutation ordered
    (fun event present => eventPermutation.mem_iff.mp present) chain nativeHistory
  obtain ⟨final, execution, pc, values⟩ := native_trace_postconditions hp clockInverse accepted
    inputs.initialization.clocks inputs.initialization.image inputs.initialization.distinct
    initialRead consistent chain nativeHistory matchedState execution
  exact ⟨final, execution, pc, values⟩

end Airbender.UnifiedReduced.Proofs
