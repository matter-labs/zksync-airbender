import Slop.Trace.CompositionCore
import Slop.Trace.Arithmetic
import Slop.Trace.WordMemory
import Human.Trace.Families.AddSub.Execution
import Slop.Trace.Terminal
import Mathlib.Data.List.Chain

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Discharge every selected original instruction against its native row.
    Decoder fields select the clause; all read/range/effect facts are derived
    by the existing family proofs. No expected instruction effect is assumed. -/
theorem row_instruction_step (profile : ISAProfile) {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (registers : ∀ index, Cell.register index ∈ cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (configuration : FlatMemoryConfiguration initial) (initialPC : trace.initial.word.Bounded)
    {row : Row p} (member : row ∈ trace.rows)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (family : entry.data.family = row.family) (query : row.decoderQuery = entry.query)
    (loads : profile = .sail → ∀ (imm : BitVec 12) (rs1 : BitVec 5),
      entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4))
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok row.start.word.toBitVec before) :
    ∃ clause, profileClause profile entry.instruction = some clause ∧
      run (normalStep clause) before =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after row.finish.word.toBitVec) := by
  cases row with
  | mk kind w =>
    cases kind with
    | addSub =>
      obtain ⟨clause, chosen, normal⟩ := local_arithmetic_instruction_execution profile hp inverse
        image trace.rom trace.memoryEpoch registers (accepted.constraints _ member)
        (accepted.active _ member)
        (arithmetic_row_ranges hp inverse accepted boundary image setup member fields query)
        fields family query loads past history
      refine ⟨clause, chosen, ?_⟩
      rw [← normal_step_rebased pc clause]
      exact normal
    | wordMemory =>
      change entry.data.family = .wordMemory at family
      have originalFields := fields
      unfold decoderFields at fields
      split at fields
      case h_1 | h_2 | h_3 | h_4 | h_5 =>
        simp only [Option.some.injEq] at fields
        rw [← fields] at family
        unfold arithmeticFields at family
        split at family <;> cases family
      case h_6 =>
        rename_i _ imm rs1 rd encoding
        change (if (rd : BitVec 5) = 0 then _ else _) = some entry.data at fields
        by_cases zero : (rd : BitVec 5) = 0
        · rw [ite_eq_left zero, Option.some.injEq] at fields
          rw [← fields] at family
          cases family
        · rw [ite_eq_right zero, Option.some.injEq] at fields
          refine ⟨SailRV32.Functions.execute_LOAD imm (.Regidx rs1) (.Regidx rd) false 4, ?_, ?_⟩
          · cases profile with
            | sail => rw [encoding]; rfl
            | airbender =>
              rw [encoding]
              unfold profileClause
              split <;> simp_all [instructionClause]
          · exact word_row_load_step hp inverse accepted boundary image setup aligned ordinary
              configuration initialPC member originalFields (by rw [← fields]) query encoding
              native past history pc
      case h_7 =>
        rename_i _ imm rs2 rs1 encoding
        refine ⟨SailRV32.Functions.execute_STORE imm (.Regidx rs2) (.Regidx rs1) 4, ?_, ?_⟩
        · cases profile <;> rw [encoding] <;> rfl
        · exact word_row_store_step hp inverse accepted boundary image setup aligned ordinary
            configuration initialPC member originalFields query encoding past history pc
      case h_8 => cases fields

set_option backward.isDefEq.respectTransparency false in
/-- The current instruction is obtained from logical decoder membership and
    preserved public bytes. Original Sail stepping is supplied by the native
    family proofs, not by a desired-read or desired-result premise. -/
theorem row_execution_step (profile : ISAProfile) {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (registers : ∀ index, Cell.register index ∈ cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (configuration : FlatMemoryConfiguration initial) (initialPC : trace.initial.word.Bounded)
    {program : List ProgramEntry} (sources : ∀ entry ∈ program, entry.Source initial)
    (code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (decoded : Decoded trace program) (loads : profile = .sail → NoDiscardedLoads program)
    {row : Row p} (member : row ∈ trace.rows)
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok row.start.word.toBitVec before) :
    Step profile program before (retiredState after row.finish.word.toBitVec) := by
  obtain ⟨entry, present, family, query⟩ := decoder_member (decoded row member)
  have source := entry_source_after_history past
    (fun event em position rom address => native_rom_unchanged
      (by dsimp [ROM.limit, timestampBase] at hp ⊢; omega) inverse accepted boundary image
      (native event em) position rom address)
    (sources entry present) (code entry present).1 (code entry present).2
  have fetched := query_pc (by dsimp [ROM.limit, limbBase] at hp ⊢; omega) query
  have step := row_instruction_step profile hp inverse accepted boundary image setup registers aligned ordinary
    configuration initialPC member source.fields family query (fun original => loads original entry present)
    native past history pc
  rw [fetched] at pc
  exact ⟨entry, present, source, pc, step⟩

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Compose all native rows in their derived order. The first step starts
    from the public state unchanged; subsequent steps reuse the existing
    history through the actual retired Sail control-register states. -/
theorem rows_execution_trace (profile : ISAProfile) {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (registers : ∀ index, Cell.register index ∈ cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (configuration : FlatMemoryConfiguration initial) (initialPC : trace.initial.word.Bounded)
    {program : List ProgramEntry} (sources : ∀ entry ∈ program, entry.Source initial)
    (code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (decoded : Decoded trace program) (loads : profile = .sail → NoDiscardedLoads program)
    (pc : run (SailRV32.Functions.get_arch_pc ()) initial = .ok trace.initial.word.toBitVec initial)
    (rows : List (Row p)) (terminal : PCState.State p) {after : State}
    (members : ∀ row ∈ rows, row ∈ trace.rows)
    (native : ∀ event ∈ (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse),
      event ∈ trace.nativeEvents)
    (chain : ((terminal, terminal) :: rows.map (fun row => (row.start, row.finish)) ++
      [(trace.initial, trace.initial)]).IsChain (fun a b => a.1 = b.2))
    (history : SailHistory cells
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse) initial after) :
    ExecutionTrace profile program initial (match rows with
      | [] => after
      | _ :: _ => retiredState after terminal.word.toBitVec) := by
  have checked := compose_native_rows pc
    (fun row member {before after events} native past current => by
      let currentPC := row.start.word.toBitVec
      have step := row_execution_step profile hp inverse accepted boundary
        (retired_state_image image currentPC) setup registers aligned ordinary
        (retired_state_configuration configuration currentPC) initialPC
        (fun entry present => entry_source_retired_state (sources entry present) currentPC)
        code decoded loads member native (retired_state_history past currentPC)
        (retired_state_history current currentPC) (retired_state_pc before currentPC)
      simpa only [retired_state_overwrite] using step)
    rows terminal members native chain history
  cases rows <;> exact checked

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Whole selected-trace soundness, from the public initial state through
    every native instruction row to the actual terminal PC and cell reads. -/
theorem restricted_trace_execution (profile : ISAProfile) {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Data p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (inputs : ExecutionBoundary trace initial cells program)
    (loads : profile = .sail → NoDiscardedLoads program)
    (accepted : Accepted trace) (decoded : Decoded trace program) :
    ∃ after, ExecutionTrace profile program initial after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
      ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok (memoryWord sink.value) after := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [ROM.limit, timestampBase] at hp ⊢; omega
  have limbSize : limbBase < p := by dsimp [ROM.limit, limbBase] at hp ⊢; omega
  obtain ⟨timestamp, initialBound⟩ := inputs.initialPC
  obtain ⟨addresses, programBound⟩ := inputs.programImage
  have initialPC := initial_pc_bound limbSize initialBound
  have initialRead := initial_state_pc limbSize initialBound
  obtain ⟨history, rows, nativeAfter, consistent, permutation, ordered, nativeHistory, matchedState⟩ :=
    decoded_row_history standardDecoderRules clockSize inverse accepted inputs.clocks inputs.image
      inputs.distinct inputs.aligned programBound decoded
  have chain := ordered_row_boundaries clockSize inverse accepted inputs.clocks permutation ordered
  have eventPermutation :
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
    rw [native_events_projection clockSize inverse accepted inputs.clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have execution := rows_execution_trace profile hp inverse accepted inputs.clocks inputs.image inputs.rom
    inputs.registers inputs.aligned inputs.ordinary inputs.configuration initialPC
    (program_sources programBound) inputs.code decoded loads initialRead rows trace.terminal
    (fun row present => permutation.mem_iff.mp present)
    (fun event present => eventPermutation.mem_iff.mp present) chain nativeHistory
  apply native_trace_postconditions clockSize inverse accepted inputs.clocks
    inputs.image inputs.distinct initialRead consistent chain nativeHistory matchedState
  cases rows <;> exact execution

end Airbender.Trace.Proofs
