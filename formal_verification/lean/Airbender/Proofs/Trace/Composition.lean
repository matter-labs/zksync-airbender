import Airbender.Proofs.Trace.CompositionCore
import Airbender.Proofs.Trace.Arithmetic

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail

/-- Imported v2 arithmetic ports retain the register address-space tag. -/
theorem native_event_register_space [Fact p.Prime] {trace : Data p}
    {event : MemoryAccess} (member : event ∈ trace.nativeEvents) :
    ∃ code, event.2.1 = Nat.pair 0 code := by
  obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨row, rowMember, present⟩ := List.mem_flatMap.mp present
  obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp present
  cases row with
  | mk family w =>
    cases family
    change port ∈ AddSub.importedConstraintsMemoryPorts.toList at portMember
    simp [AddSub.importedConstraintsMemoryPorts] at portMember
    rcases portMember with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- Actual initialized history identifies canonical GPR cells; native metadata
    excludes RAM, so every code byte survives even outside the tracked domain. -/
theorem native_history_memory [Fact p.Prime] {trace : Data p} {cells : List Cell}
    {events : List MemoryAccess} {before after : State}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (history : SailHistory cells events before after) : after.mem = before.mem := by
  apply register_history_memory history
  intro event member
  obtain ⟨cell, _, address⟩ := history_address_member history member
  cases cell with
  | register index => exact ⟨index, address.symm⟩
  | ram pc =>
    obtain ⟨code, space⟩ := native_event_register_space (native event member)
    have impossible := address.trans space
    change Nat.pair 1 _ = Nat.pair 0 _ at impossible
    have different := (Nat.pair_eq_pair.mp impossible).1
    omega

/-- Public bytes are preserved by actual native GPR transfers. Successful setup
    construction supplies pure original decoder evidence for every later state. -/
theorem entry_source_after_native_history [Fact p.Prime] {trace : Data p}
    {cells : List Cell} {events : List MemoryAccess} {initial before : State}
    {entry : ProgramEntry} (source : entry.Source initial)
    (pureDecoder : SailRV32.Functions.encdec_backwards entry.bits = .pure entry.instruction)
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (history : SailHistory cells events initial before) : entry.Source before :=
  ⟨read_word_frame (native_history_memory native history) source.bytes,
    by rw [pureDecoder]; rfl, source.fields⟩

/-- All native rows compose through actual fetched/decoded original Sail steps.
    Acceptance and public constructors derive row order, intermediate states,
    local interfaces, retirement and terminal register/RAM values. -/
theorem image_execution_soundness [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {trace : Data p} {setup : DecoderSetup} {initial : State} {cells : List Cell}
    {count logCapacity : Nat} (inputs : ImageBoundary trace initial cells)
    (image : decoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Realizes (StepWith decoderFields registerClause setup.program) trace initial cells := by
  have large : limbBase < p := by dsimp [limbBase, timestampBase] at *; omega
  have clocks := image_clock_boundary (by dsimp [timestampBase] at hp; omega) inputs
  have pureDecoders := setup_decoders_pure image
  obtain ⟨history, rows, nativeAfter, consistent, permutation, ordered, nativeHistory, matched⟩ :=
    decoded_row_history hp accepted clocks inputs.image inputs.domain aligned decoded
  have chain := ordered_row_boundaries hp accepted clocks permutation ordered
  have events : (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm
      trace.nativeEvents := by
    rw [native_events_projection hp accepted clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have pc := initial_state_pc large inputs.initial
  have step : ∀ row ∈ trace.rows, ∀ {before after : State} {past : List MemoryAccess},
      (∀ event ∈ past, event ∈ trace.nativeEvents) →
      SailHistory cells past initial before →
      SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after →
      StepWith decoderFields registerClause setup.program (retiredState before row.start.word.toBitVec)
        (retiredState after row.finish.word.toBitVec) := by
    intro row member before after past native earlier current
    obtain ⟨entry, present, source, query⟩ := decoded_sources
      (by dsimp [limbBase] at large; omega) image accepted decoded row member
    have replay := pureDecoders entry present
    have sourceHere := entry_source_after_native_history source replay native earlier
    have canonical := native_query_pc_word large query
    change row.start.word = Word.ofBitVec entry.pc at canonical
    have pcWord : row.start.word.toBitVec = entry.pc := by
      rw [canonical, Word.ofBitVec_roundtrip]
    refine ⟨entry, present, entry_source_retired_state sourceHere _ replay, ?_, ?_⟩
    · simpa only [pcWord] using retired_state_pc before row.start.word.toBitVec
    · cases row with
      | mk family w =>
        cases family
        exact arithmetic_instruction_execution hp inputs image accepted decoded member source.fields query current
  have execution := compose_native_rows pc pureDecoders step rows trace.terminal
    (fun row member => permutation.mem_iff.mp member)
    (fun event member => events.mem_iff.mp member) chain nativeHistory
  exact native_trace_postconditions hp accepted clocks inputs.image inputs.domain pc
    consistent chain nativeHistory matched execution

end Airbender.Trace.Proofs
