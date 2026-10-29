import Airbender.Proofs.UnifiedReduced.StreamCalls
import Airbender.Proofs.UnifiedReduced.ModularDecoder
import Airbender.Proofs.Trace.NonDeterminism
import Airbender.Proofs.UnifiedReduced.MixedMemory

namespace Airbender.UnifiedReduced.Caller.Stream.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

/-- The external registry admits exactly a read or an architectural hint. -/
theorem external_fields_cases {instruction : SailRV32.instruction}
    {data : DecoderData UnifiedFamily}
    (fields : Stream.externalDecoderFields instruction = some data) :
    (∃ rd : BitVec 5, rd ≠ 0 ∧
      instruction = .CSRReg (0x7C0, .Regidx 0, .Regidx rd, .CSRRW) ∧
      data = ⟨.machine, 0, 0, rd, ⟨0, 0⟩, 256, 0⟩) ∨
    (∃ rs1 : BitVec 5, rs1 ≠ 0 ∧
      instruction = .CSRReg (0x7C0, .Regidx rs1, .Regidx 0, .CSRRW) ∧
      data = ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩) := by
  cases instruction <;> try cases fields
  case CSRReg args =>
    rcases args with ⟨csr, rs1, rd, operation⟩
    cases operation <;> try cases fields
    cases rs1 with
    | Regidx source =>
      cases rd with
      | Regidx destination =>
        change BitVec 5 at source destination
        by_cases selected : csr = 0x7C0#12
        all_goals by_cases sourceZero : source = 0#5
        all_goals by_cases destinationZero : destination = 0#5
        all_goals simp_all [Stream.externalDecoderFields,
          NonDeterminism.decoderFields, DecoderData.mapFamily]

/-- Split the combined public registry without any witness selector premise. -/
theorem fields_cases {instruction : SailRV32.instruction}
    {data : DecoderData UnifiedFamily}
    (fields : Stream.decoderFields instruction = some data) :
    Modular.decoderFields instruction = some data ∨
      Stream.externalDecoderFields instruction = some data := by
  unfold Stream.decoderFields at fields
  cases ordinary : Modular.decoderFields instruction with
  | none => exact Or.inr (by simpa [ordinary] using fields)
  | some original => exact Or.inl (by simpa [ordinary] using fields)

theorem field_bounds {instruction : SailRV32.instruction}
    {data : DecoderData UnifiedFamily}
    (fields : Stream.decoderFields instruction = some data) :
    data.immediate.Bounded ∧ data.mask < 524288 ∧ data.funct3 < 55 := by
  rcases fields_cases fields with ordinary | external
  · rcases Modular.Proofs.fields_cases ordinary with mixed | modular
    · exact Mixed.Proofs.field_bounds mixed
    · exact Modular.Proofs.mop_bounds modular
  · rcases external_fields_cases external with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
    all_goals norm_num [Word.Bounded, limbBase]

/-- Every admitted write to x0 has a native zero-preserving selector form. -/
theorem decoder_zero_cases {instruction : SailRV32.instruction}
    {data : DecoderData UnifiedFamily}
    (fields : Stream.decoderFields instruction = some data) (zero : data.rd = 0) :
    data = ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ ∨
      (data.mask.testBit 14 = true ∧
        ∃ i : Fin 4, data.mask.testBit (10 + i.val) = true) ∨
      data.mask.testBit 18 = true := by
  rcases fields_cases fields with ordinary | external
  · rcases Modular.Proofs.fields_cases ordinary with mixed | modular
    · rcases Mixed.Proofs.fields_cases mixed with standard | custom
      · exact UnifiedReduced.Proofs.decoder_zero_cases standard zero
      · exact False.elim (UnifiedReduced.Proofs.custom_field_nonzero custom zero)
    · exact Or.inl (Modular.Proofs.mop_zero_cases modular zero)
  · rcases external_fields_cases external with ⟨rd, nonzero, _, equal⟩ | ⟨_, _, _, equal⟩
    · rw [equal] at zero
      exact False.elim (nonzero zero)
    · exact Or.inl equal

/-- Derive ordinary-row x0 preservation from the stream program and native gates. -/
theorem ordinary_zero_preserving_of_program [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 524288)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : State} {addresses : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program)
    (image : programImageRunWith Stream.decoderFields before addresses = some program)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows)
    (ordinary : row ∉ data.callers) : RowZeroPreserving row := by
  cases row with
  | mk family assignment =>
    cases family
    have core := Verification.holds_of_sublist (accepted.constraints _ member)
      (List.sublist_append_left (importedConstraints data.machine.rom)
        importedConstraintsTimestampLookups)
    obtain ⟨entry, present, _, query⟩ :=
      decoder_member (accepted.ordinaryDecoded _ member ordinary)
    have source := run_program_sources image entry present
    exact UnifiedReduced.Proofs.row_zero_preserving_of_metadata hp core
      (accepted.active _ member) query
      (UnifiedReduced.Proofs.decoder_selectors hp core (field_bounds source.fields).2.1 query)
      (decoder_zero_cases source.fields)

/-- Exact shared-memory matching preserves x0 across stream rows and workers. -/
theorem mixed_zero_rules_of_program [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase) (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {before : State} {callerAddresses addresses : List (BitVec 32)}
    (accepted : MixedMemoryAccepted data program)
    (publicProgram : RequestInputs data before callerAddresses)
    (image : programImageRunWith Stream.decoderFields before addresses = some program)
    (requests : RequestBinding data before) :
    Transfer.CellWriteRules (Caller.Proofs.mixedData data) (Cell.register 0).addressCode 0 :=
  Caller.Proofs.mixed_zero_rules_of_preserving hp inverse accepted publicProgram
    (fun _ member ordinary => ordinary_zero_preserving_of_program
      (by dsimp [timestampBase] at hp; omega) accepted image member ordinary) requests

end Airbender.UnifiedReduced.Caller.Stream.Proofs
