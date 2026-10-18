import Airbender.Proofs.Trace.ProjectedTerminal
import Airbender.Proofs.Trace.Families.WordMemory.AddressDomain
import Airbender.Proofs.Trace.Families.WordMemory.Execution
import Airbender.Review.Trace.Families.WordMemory.Execution

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Verification
open _root_.Sail.ArchSem

set_option backward.isDefEq.respectTransparency false in
/-- Accepted native rows compose through original fetched/decoded LW/SW steps.
    Public initialization derives row order, states, reads, ranges and exact
    terminal cells. Public cell/seed domains supply ordinary RAM and ROM coverage. -/
theorem image_execution_soundness [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus WordMemoryFamily} {setup : DecoderSetup}
    {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity romCount : Nat}
    (inputs : ShadowImageBoundary trace initial cells seeds)
    (decoder : decoderSetupImage initial count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (configuration : FlatMemoryConfiguration initial)
    (image : wordROMImage initial romCount = some trace.rom)
    (programROM : count ≤ 1048576)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (covered : ∀ seed ∈ seeds, seed.1.toNat < 4 * romCount) :
    WordMemory.Realizes setup.program trace initial cells := by
  have clocks := shadow_clock_boundary (by decide) inputs
  have pureDecoders := setup_decoders_pure decoder
  obtain ⟨history, rows, nativeAfter, consistent, permutation, ordered, nativeHistory, matched⟩ :=
    projected_row_history (by decide) inputs accepted decoded aligned
  have chain := Trace.Proofs.ordered_row_boundaries (by decide) accepted clocks permutation ordered
  have events : (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm
      trace.nativeEvents := by
    rw [Trace.Proofs.native_events_projection (by decide) accepted clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have pc := Trace.Proofs.initial_state_pc (by decide) inputs.initial
  have step : ∀ row ∈ trace.rows, ∀ {before after : State} {past : List MemoryAccess},
      (∀ event ∈ past, event ∈ trace.nativeEvents) →
      SailHistory cells (past.filter fun event => architecturalAddress event.2.1) initial before →
      SailHistory cells ((rowEvents trace.memoryEpoch row).reverse.filter
        fun event => architecturalAddress event.2.1) before after →
      StepWith decoderFields instructionClause setup.program (retiredState before row.start.word.toBitVec)
        (retiredState after row.finish.word.toBitVec) := by
    intro row member before after past _native earlier current
    obtain ⟨entry, present, source, query⟩ := decoded_sources (by decide) decoder accepted decoded row member
    have replay := pureDecoders entry present
    have sourceHere := setup_sources_after_history inputs.architectural earlier decoder programROM entry present
    have canonical := Trace.Proofs.native_query_pc_word (by decide) query
    change row.start.word = Word.ofBitVec entry.pc at canonical
    have pcWord : row.start.word.toBitVec = entry.pc := by
      rw [canonical, Word.ofBitVec_roundtrip]
    refine ⟨entry, present, Trace.Proofs.entry_source_retired_state sourceHere _ replay, ?_, ?_⟩
    · simpa only [pcWord] using Trace.Proofs.retired_state_pc before row.start.word.toBitVec
    · cases row with
      | mk family w =>
        cases family
        have domains := initialized_address_domains (by decide) inputs accepted ordinary covered member
        exact initialized_instruction_retirement inputs decoder accepted decoded member source.fields query
          (Trace.Proofs.sail_history_configuration earlier configuration)
          (rom_image_after_frame (projected_history_rom_bytes inputs.architectural earlier) image)
          domains.1 domains.2 current
  have execution := Trace.Proofs.compose_projected_rows architecturalAddress pc pureDecoders step rows trace.terminal
    (fun row member => permutation.mem_iff.mp member)
    (fun event member => events.mem_iff.mp member) chain nativeHistory
  exact Trace.Proofs.projected_trace_postconditions (by decide) accepted clocks architecturalAddress
    (shadow_image_projection inputs) (shadow_image_unique inputs) pc consistent chain nativeHistory matched execution

end Airbender.WordMemory.Proofs
