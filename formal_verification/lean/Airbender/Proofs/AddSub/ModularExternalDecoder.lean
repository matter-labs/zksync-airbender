import Airbender.Review.Trace.Modular.External
import Airbender.Proofs.AddSub.ModularProgram
import Airbender.Proofs.Trace.NonDeterminism
import Airbender.Proofs.Trace.OracleExecution

namespace Airbender.AddSub.Modular.External.Proofs
open Arithmetic Trace Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

theorem arithmetic_cases {original : SailRV32.instruction} {data : DecoderData}
    (fields : arithmeticDecoderFields original = some data) :
    NonDeterminism.decoderFields original = some data ∨
      ∃ opcode rs1 rs2 rd, original = Modular.instruction opcode rs1 rs2 rd ∧
        data = nativeData opcode rs1 rs2 rd := by
  unfold arithmeticDecoderFields at fields
  split at fields
  · rcases Modular.Proofs.fields_cases fields with standard | custom
    · simp [Trace.decoderFields] at standard
    · exact Or.inr custom
  · exact Or.inl fields

theorem standard_fields {original : SailRV32.instruction} {data : DecoderData}
    (fields : Trace.decoderFields original = some data) :
    arithmeticDecoderFields original = some data := by
  unfold arithmeticDecoderFields
  split
  · simp [Trace.decoderFields] at fields
  · exact NonDeterminism.Proofs.standard_fields fields

theorem field_bounds {original : SailRV32.instruction} {data : DecoderData}
    (fields : arithmeticDecoderFields original = some data) :
    data.immediate.Bounded ∧ data.mask < 512 := by
  rcases arithmetic_cases fields with oracle | ⟨opcode, rs1, rs2, rd, _, rfl⟩
  · exact NonDeterminism.Proofs.field_bounds oracle
  · unfold nativeData arithmeticFields
    split
    · exact ⟨by constructor <;> decide, by decide⟩
    · exact ⟨Word.ofBitVec_bound 0, by change 2 ^ (opcode.selector - 10) < 512; cases opcode <;> decide⟩

theorem memory_fields {original : SailRV32.instruction} {data : DecoderData}
    (fields : arithmeticDecoderFields original = some data) (family : data.family = .wordMemory) :
    Trace.decoderFields original = some data := by
  rcases arithmetic_cases fields with oracle | ⟨opcode, rs1, rs2, rd, _, rfl⟩
  · exact NonDeterminism.Proofs.memory_fields oracle family
  · rw [Modular.Proofs.native_family] at family
    cases family

def decoderRules : DecoderRules arithmeticDecoderFields where
  bounds _ _ := field_bounds
  zeroNop _ _ fields family zero := by
    rcases arithmetic_cases fields with oracle | ⟨opcode, rs1, rs2, rd, _, rfl⟩
    · exact NonDeterminism.Proofs.decoderRules.zeroNop _ _ oracle family zero
    · rw [Modular.Proofs.native_rd] at zero
      subst rd
      rfl
  loadNonzero _ _ fields family load := decoder_load_nonzero (memory_fields fields family) family load

theorem fields_cases {original : SailRV32.instruction} {data : DecoderData PooledFamily}
    (fields : External.decoderFields original = some data) :
    (∃ d, arithmeticDecoderFields original = some d ∧
      data = d.mapFamily pooledArithmeticFamily) ∨ pooledDecoderFields original = some data := by
  unfold External.decoderFields at fields
  cases selected : arithmeticDecoderFields original with
  | none => exact Or.inr (by simpa [selected] using fields)
  | some original =>
    exact Or.inl ⟨original, rfl, (Option.some.inj (by simpa [selected] using fields)).symm⟩

theorem source_cases {before : Reference.RiscV.Sail.State} {entry : PooledProgramEntry}
    (source : entry.SourceWith before External.decoderFields) :
    PooledSource before entry arithmeticDecoderFields := by
  rcases fields_cases source.fields with ⟨data, fields, equal⟩ | fields
  · exact Or.inl ⟨⟨entry.pc, entry.bits, entry.instruction, data⟩,
      ⟨source.bytes, source.decoded, fields⟩, by cases entry; simp_all [ProgramEntry.mapFamily]⟩
  · have original : entry.SourceWith before pooledDecoderFields := ⟨source.bytes, source.decoded, fields⟩
    rcases pooled_source_cases original with base | branch | multiply | shift | memory
    · obtain ⟨originalEntry, originalSource, equal⟩ := base
      exact Or.inl ⟨originalEntry, ⟨originalSource.bytes, originalSource.decoded,
        standard_fields originalSource.fields⟩, equal⟩
    · exact Or.inr (Or.inl branch)
    · exact Or.inr (Or.inr (Or.inl multiply))
    · exact Or.inr (Or.inr (Or.inr (Or.inl shift)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr memory)))

instance combinedRegistry : PooledRegistry External.decoderFields where
  arithmeticProjection := arithmeticDecoderFields
  rules := decoderRules
  memoryFields := memory_fields
  sourceCases := source_cases

theorem clause_standard [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {original : SailRV32.instruction} {data : DecoderData}
    (fields : Trace.decoderFields original = some data)
    {stream : List (BitVec 32)} {position : Nat}
    {body : SailRV32.SailM SailRV32.ExecutionResult}
    (selected : profileClause .sail original = some body) :
    External.clause stream position original = some (body, position) := by
  unfold External.clause
  split
  · simp [Trace.decoderFields] at fields
  · exact NonDeterminism.Proofs.clause_standard fields selected

theorem clause_original [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {original : SailRV32.instruction} {stream : List (BitVec 32)} {position : Nat}
    {body : SailRV32.SailM SailRV32.ExecutionResult}
    (selected : instructionClause original = some body) :
    External.clause stream position original = some (body, position) := by
  unfold External.clause
  split
  · simp [instructionClause, Reference.RiscV.Sail.registerClause] at selected
  · exact NonDeterminism.Proofs.clause_original selected

end Airbender.AddSub.Modular.External.Proofs
