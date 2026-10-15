import Airbender.Proofs.AddSub.ModularDecoder

namespace Airbender.AddSub.Modular.Pooled.Proofs
open Arithmetic Trace Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

theorem fields_cases {instruction : SailRV32.instruction} {data : DecoderData PooledFamily}
    (fields : Pooled.decoderFields instruction = some data) :
    (∃ d, Modular.decoderFields instruction = some d ∧
      data = d.mapFamily pooledArithmeticFamily) ∨
      pooledDecoderFields instruction = some data := by
  unfold Pooled.decoderFields at fields
  cases selected : Modular.decoderFields instruction with
  | none => exact Or.inr (by simpa [selected] using fields)
  | some original =>
    exact Or.inl ⟨original, rfl, (Option.some.inj (by simpa [selected] using fields)).symm⟩

theorem source_cases {before : Reference.RiscV.Sail.State} {entry : PooledProgramEntry}
    (source : entry.SourceWith before Pooled.decoderFields) :
    PooledSource before entry Modular.decoderFields := by
  rcases fields_cases source.fields with ⟨data, fields, equal⟩ | fields
  · exact Or.inl ⟨⟨entry.pc, entry.bits, entry.instruction, data⟩,
      ⟨source.bytes, source.decoded, fields⟩, by cases entry; simp_all [ProgramEntry.mapFamily]⟩
  · have original : entry.SourceWith before pooledDecoderFields :=
      ⟨source.bytes, source.decoded, fields⟩
    rcases pooled_source_cases original with base | branch | multiply | shift | memory
    · obtain ⟨originalEntry, originalSource, equal⟩ := base
      exact Or.inl ⟨originalEntry, ⟨originalSource.bytes, originalSource.decoded,
        Modular.Proofs.standard_fields originalSource.fields⟩, equal⟩
    · exact Or.inr (Or.inl branch)
    · exact Or.inr (Or.inr (Or.inl multiply))
    · exact Or.inr (Or.inr (Or.inr (Or.inl shift)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr memory)))

instance modularPooledRegistry : PooledRegistry Pooled.decoderFields where
  arithmeticProjection := Modular.decoderFields
  rules := Modular.Proofs.decoderRules
  memoryFields := Modular.Proofs.memory_fields
  sourceCases := source_cases

theorem clause_original [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {instruction : SailRV32.instruction} {original : SailRV32.SailM SailRV32.ExecutionResult}
    (selected : instructionClause instruction = some original) :
    Pooled.clauseFor instruction = some original := by
  unfold Pooled.clauseFor
  split <;> simp_all [instructionClause, Reference.RiscV.Sail.registerClause]

end Airbender.AddSub.Modular.Pooled.Proofs
