import Airbender.Review.UnifiedReduced.MixedExecution
import Airbender.Proofs.UnifiedReduced.CustomHistory

namespace Airbender.UnifiedReduced.Mixed.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem fields_cases {instruction : SailRV32.instruction} {data : DecoderData UnifiedFamily}
    (fields : Mixed.decoderFields instruction = some data) :
    UnifiedReduced.decoderFields instruction = some data ∨ customDecoderFields instruction = some data := by
  unfold Mixed.decoderFields at fields
  cases standard : UnifiedReduced.decoderFields instruction with
  | none => exact Or.inr (by simpa [standard] using fields)
  | some original =>
    have equal : original = data := by simpa [standard] using fields
    exact Or.inl (congrArg some equal)

theorem field_bounds {instruction : SailRV32.instruction} {data : DecoderData UnifiedFamily}
    (fields : Mixed.decoderFields instruction = some data) :
    data.immediate.Bounded ∧ data.mask < 524288 ∧ data.funct3 < 55 := by
  rcases fields_cases fields with standard | custom
  · exact UnifiedReduced.Proofs.decoder_field_bounds standard
  · exact UnifiedReduced.Proofs.custom_field_bounds custom

theorem zero_preserving [Fact p.Prime] (hp : 524288 < p) {trace : UnifiedTrace p}
    (accepted : Accepted trace) {initial : State}
    {addresses : List (BitVec 32)} {program : List UnifiedReduced.ProgramEntry}
    (image : Mixed.programImage initial addresses = some program) (decoded : UnifiedReduced.Decoded trace program) :
    ZeroPreserving trace := by
  intro row member
  cases row with
  | mk kind w =>
    cases kind
    have core := Verification.holds_of_sublist (accepted.constraints _ member)
      (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
    obtain ⟨entry, present, _, query⟩ := decoder_member (decoded _ member)
    have source := run_program_sources image entry present
    rcases fields_cases source.fields with standard | custom
    · have fetched : Fetched w initial :=
        ⟨entry, ⟨source.bytes, source.decoded, standard⟩, query,
          UnifiedReduced.Proofs.decoder_selectors hp core
            (UnifiedReduced.Proofs.decoder_field_bounds standard).2.1 query⟩
      exact UnifiedReduced.Proofs.row_zero_preserving hp core (accepted.active _ member) fetched
    · exact UnifiedReduced.Proofs.custom_row_zero_preserving hp core custom query

theorem memory_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : UnifiedTrace p}
    (accepted : Accepted trace) {initial : State} {cells : List Cell} {program : List UnifiedReduced.ProgramEntry}
    (inputs : NativeInputs Mixed.decoderFields trace initial cells program)
    (decoded : UnifiedReduced.Decoded trace program) : MemoryExecution trace initial cells := by
  obtain ⟨addresses, image⟩ := inputs.programImage
  have zero := zero_preserving (by dsimp [timestampBase] at hp; omega) accepted image decoded
  exact Trace.Proofs.native_row_history hp inverse accepted inputs.clocks inputs.image inputs.distinct inputs.aligned
    (Trace.Proofs.zero_writes_of_preserving hp inverse accepted inputs.clocks inputs.image zero)

theorem source_after_history [Fact p.Prime] (hp : 131072 < p)
    {trace : UnifiedTrace p} (accepted : Accepted trace)
    {initial before : State} {cells : List Cell} {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    {entry : UnifiedReduced.ProgramEntry} (source : entry.SourceWith initial Mixed.decoderFields)
    (code : entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0) :
    entry.SourceWith before Mixed.decoderFields :=
  entry_source_after_history past
    (fun event member pc inROM address => UnifiedReduced.Proofs.native_rom_unchanged hp accepted
      (native event member) pc inROM address) source code.1 code.2

end Airbender.UnifiedReduced.Mixed.Proofs
