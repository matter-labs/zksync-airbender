import Airbender.Review.Compiler.ProgramLogicalRows
import Airbender.Proofs.GKRProtocol.LogicalRows

namespace Airbender.Compiler
set_option warningAsError true
set_option Elab.async false

namespace PooledExecution

/-- The physical native input proves the execute bit for either cache mode. -/
theorem ProgramLogicalRowCertificate.row_active {tables : ProgramLookupRows}
    (cert : ProgramLogicalRowCertificate tables) :
    cert.row.assignment cert.row.columns.execute = 1 := by
  cases cert with
  | addSubUncached input _arguments => exact PooledRowNative.AddSubUncached.input_active input
  | addSubCached input _arguments => exact PooledRowNative.AddSubCached.input_active input
  | jumpBranchUncached input _arguments => exact PooledRowNative.JumpBranchUncached.input_active input
  | jumpBranchCached input _arguments => exact PooledRowNative.JumpBranchCached.input_active input
  | mulDivUncached input _arguments => exact PooledRowNative.MulDivUncached.input_active input
  | mulDivCached input _arguments => exact PooledRowNative.MulDivCached.input_active input
  | shiftBinopUncached input _arguments => exact PooledRowNative.ShiftBinopUncached.input_active input
  | shiftBinopCached input _arguments => exact PooledRowNative.ShiftBinopCached.input_active input
  | wordMemoryUncached input _arguments => exact PooledRowNative.WordMemoryUncached.input_active input
  | wordMemoryCached input _arguments => exact PooledRowNative.WordMemoryCached.input_active input
  | subwordMemoryUncached input _arguments => exact PooledRowNative.SubwordMemoryUncached.input_active input
  | subwordMemoryCached input _arguments => exact PooledRowNative.SubwordMemoryCached.input_active input

/-- Exact matching and native operand transport supply the source tuple.
The public setup interpretation remains a separate boundary. -/
theorem ProgramLogicalRowCertificate.source_member {tables : ProgramLookupRows}
    (cert : ProgramLogicalRowCertificate tables) (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ cert.sourceRequests group) (enabled : query.weight ≠ 0) :
    ∃ index : Fin cert.lookupLength, query.fields = tables cert.configuration group index.val := by
  cases cert with
  | addSubUncached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.AddSubUncached.source_member_with
      (fun group index => tables .addSubUncached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
  | addSubCached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.AddSubCached.source_member_with
      (fun group index => tables .addSubCached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
  | jumpBranchUncached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.JumpBranchUncached.source_member_with
      (fun group index => tables .jumpBranchUncached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
  | jumpBranchCached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.JumpBranchCached.source_member_with
      (fun group index => tables .jumpBranchCached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
  | mulDivUncached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.MulDivUncached.source_member_with
      (fun group index => tables .mulDivUncached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
  | mulDivCached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.MulDivCached.source_member_with
      (fun group index => tables .mulDivCached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
  | shiftBinopUncached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.ShiftBinopUncached.source_member_with
      (fun group index => tables .shiftBinopUncached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
  | shiftBinopCached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.ShiftBinopCached.source_member_with
      (fun group index => tables .shiftBinopCached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
  | wordMemoryUncached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.WordMemoryUncached.source_member_with
      (fun group index => tables .wordMemoryUncached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
  | wordMemoryCached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.WordMemoryCached.source_member_with
      (fun group index => tables .wordMemoryCached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
  | subwordMemoryUncached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.SubwordMemoryUncached.source_member_with
      (fun group index => tables .subwordMemoryUncached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
  | subwordMemoryCached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.SubwordMemoryCached.source_member_with
      (fun group index => tables .subwordMemoryCached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩

end PooledExecution

namespace UnifiedExecution

/-- The physical native input proves the execute bit for either cache mode. -/
theorem ProgramLogicalRowCertificate.row_active {tables : ProgramLookupRows}
    (cert : ProgramLogicalRowCertificate tables) :
    cert.row.assignment cert.row.columns.execute = 1 := by
  cases cert with
  | unifiedUncached input _arguments => exact UnifiedRowNative.UnifiedUncached.input_active input
  | unifiedCached input _arguments => exact UnifiedRowNative.UnifiedCached.input_active input

/-- Exact matching and native operand transport supply the source tuple.
The public setup interpretation remains a separate boundary. -/
theorem ProgramLogicalRowCertificate.source_member {tables : ProgramLookupRows}
    (cert : ProgramLogicalRowCertificate tables) (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ cert.sourceRequests group) (enabled : query.weight ≠ 0) :
    ∃ index : Fin cert.lookupLength, query.fields = tables cert.configuration group index.val := by
  cases cert with
  | unifiedUncached input arguments =>
    obtain ⟨index, same⟩ := UnifiedRowNative.UnifiedUncached.source_member_with
      (fun group index => tables .unifiedUncached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
  | unifiedCached input arguments =>
    obtain ⟨index, same⟩ := UnifiedRowNative.UnifiedCached.source_member_with
      (fun group index => tables .unifiedCached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩

end UnifiedExecution

end Airbender.Compiler
