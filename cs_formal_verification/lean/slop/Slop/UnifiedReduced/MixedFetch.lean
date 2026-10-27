import Human.Helpers.UnifiedReduced.MixedFetch
import Slop.UnifiedReduced.MixedMemory
import Slop.Trace.CodeHistory

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem source_after_ram_history {Kind : Type}
    {projection : SailRV32.instruction → Option (DecoderData Kind)} {cells : List Cell} {events : List MemoryAccess}
    {initial before : State} (history : SailHistory cells events initial before)
    (ram : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat)
    {entry : Trace.ProgramEntry Kind} (source : entry.SourceWith initial projection)
    (code : entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0) :
    entry.SourceWith before projection := by
  exact ⟨history_code_frame_of_domain history ram entry.pc code.1 code.2 source.bytes,
    source.decoded, source.fields⟩

theorem cycle_source {Kind : Type} {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {cells : List Cell} {events : List MemoryAccess} {initial before : State}
    {row : Trace.Row p UnifiedFamily} {entry : Trace.ProgramEntry Kind}
    (past : SailHistory cells (events.filter fun event => decide (event.1 ≤ row.clock)) initial before)
    (source : entry.SourceWith initial projection)
    (ram : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat)
    (code : entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (pc : row.start.word.toBitVec = entry.pc) :
    entry.SourceWith (retiredState before row.start.word.toBitVec) projection := by
  have current := source_after_ram_history past ram source code
  rw [pc]
  have bytes := cell_read_nextPC (.ram entry.pc) current.bytes entry.pc
  have bytes := cell_read_PC (.ram entry.pc) bytes entry.pc
  exact ⟨bytes, current.decoded, current.fields⟩

theorem current_fetch_of_history
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (code : CodeProfile data program cells) {events : List MemoryAccess} {finalState : State}
    (order : events.Pairwise (fun a b => b.1 ≤ a.1)) (history : SailHistory cells events initial finalState) :
    CurrentFetch data program initial cells events := by
  have reachable (row : Trace.Row babyBearModulus UnifiedFamily) (member : row ∈ data.machine.rows) :
      ∃ before, SailHistory cells (events.filter fun event => decide (event.1 ≤ row.clock)) initial before := by
    have clocks := machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram member
    obtain ⟨before, after, _, past, _, _⟩ := history_window order history
      (by omega : Delegation.Caller.startClock row ≤ Delegation.Caller.finishClock row)
    exact ⟨before, past⟩
  refine ⟨?_, ?_⟩
  · intro row member ordinary
    obtain ⟨entry, present, _, query⟩ := decoder_member (accepted.ordinaryDecoded row member ordinary)
    have source := run_program_sources inputs.ordinaryProgram entry present
    have pcWord : row.start.word = Word.ofBitVec entry.pc := by
      cases row with
      | mk kind w =>
        cases kind
        exact native_query_pc_word (by decide) query
    have pc : row.start.word.toBitVec = entry.pc := (congrArg Word.toBitVec pcWord).trans (Word.ofBitVec_roundtrip _)
    refine ⟨reachable row member, entry, present, query, pc, ?_⟩
    intro before past
    exact cycle_source past source code.ram (code.ordinary entry present) pc
  · intro row member
    have decoded := accepted.decoded row member
    change ∃ i : Fin data.program.length, row.decoderQuery = Delegation.Caller.query (data.program.get i) at decoded
    obtain ⟨i, query⟩ := decoded
    let entry := data.program.get i
    have present : entry ∈ data.program := List.get_mem _ _
    have source := run_program_sources inputs.publicProgram.image entry present
    have pcWord : row.start.word = Word.ofBitVec entry.pc := by
      have low := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[0]) query
      have high := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[1]) query
      cases row with
      | mk kind w =>
        cases kind
        exact word_of_pc_query (by decide) low high
    have pc : row.start.word.toBitVec = entry.pc := (congrArg Word.toBitVec pcWord).trans (Word.ofBitVec_roundtrip _)
    refine ⟨reachable row (List.mem_of_mem_filter member), entry, present, query, pc, ?_⟩
    intro before past
    exact cycle_source past source code.ram (code.callers entry present) pc

theorem current_fetch
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (code : CodeProfile data program cells) :
    ∃ events finalState, events.Perm (data.mixedSteps.map transferEvent) ∧
      SailHistory cells events initial finalState ∧ CurrentFetch data program initial cells events := by
  have effects := mixed_memory_effects accepted inputs
  obtain ⟨events, finalState, permutation, order, history, _, _, _⟩ := effects.execution
  exact ⟨events, finalState, permutation, history, current_fetch_of_history accepted inputs code order history⟩

end Airbender.UnifiedReduced.Caller.Proofs
