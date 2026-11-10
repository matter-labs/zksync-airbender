import Airbender.Review.Compiler.ProgramLogicalRows
import Airbender.Proofs.GKRProtocol.ProgramNativeTransport

namespace Airbender.Compiler
set_option warningAsError true
set_option Elab.async false

namespace PooledExecution

/-- The physical native input proves the execute bit for the cached circuit. -/
theorem ProgramLogicalRowCertificate.row_active {tables : ProgramLookupRows}
    (cert : ProgramLogicalRowCertificate tables) :
    cert.row.assignment cert.row.columns.execute = 1 := by
  cases cert with
  | addSubCached input _arguments => exact PooledRowNative.AddSubCached.input_active input
  | jumpBranchCached input _arguments => exact PooledRowNative.JumpBranchCached.input_active input
  | mulDivCached input _arguments => exact PooledRowNative.MulDivCached.input_active input
  | shiftBinopCached input _arguments => exact PooledRowNative.ShiftBinopCached.input_active input
  | wordMemoryCached input _arguments => exact PooledRowNative.WordMemoryCached.input_active input
  | subwordMemoryCached input _arguments => exact PooledRowNative.SubwordMemoryCached.input_active input

/-- Exact matching and native operand transport supply the source tuple.
The public setup interpretation remains a separate boundary. -/
theorem ProgramLogicalRowCertificate.source_member {tables : ProgramLookupRows}
    (cert : ProgramLogicalRowCertificate tables) (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ cert.sourceRequests group) (enabled : query.weight ≠ 0) :
    ∃ index : Fin cert.lookupLength, query.fields = tables cert.configuration group index.val := by
  cases cert with
  | addSubCached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.AddSubCached.source_member_with
      (fun group index => tables .addSubCached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
  | jumpBranchCached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.JumpBranchCached.source_member_with
      (fun group index => tables .jumpBranchCached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
  | mulDivCached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.MulDivCached.source_member_with
      (fun group index => tables .mulDivCached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
  | shiftBinopCached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.ShiftBinopCached.source_member_with
      (fun group index => tables .shiftBinopCached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
  | wordMemoryCached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.WordMemoryCached.source_member_with
      (fun group index => tables .wordMemoryCached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩
  | subwordMemoryCached input arguments =>
    obtain ⟨index, same⟩ := PooledRowNative.SubwordMemoryCached.source_member_with
      (fun group index => tables .subwordMemoryCached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩

end PooledExecution

namespace UnifiedExecution

/-- The physical native input proves the execute bit for the cached circuit. -/
theorem ProgramLogicalRowCertificate.row_active {tables : ProgramLookupRows}
    (cert : ProgramLogicalRowCertificate tables) :
    cert.row.assignment cert.row.columns.execute = 1 := by
  cases cert with
  | unifiedCached input _arguments => exact UnifiedRowNative.UnifiedCached.input_active input

/-- Exact matching and native operand transport supply the source tuple.
The public setup interpretation remains a separate boundary. -/
theorem ProgramLogicalRowCertificate.source_member {tables : ProgramLookupRows}
    (cert : ProgramLogicalRowCertificate tables) (group : Fin 3) (query : MaterializedQuery)
    (member : query ∈ cert.sourceRequests group) (enabled : query.weight ≠ 0) :
    ∃ index : Fin cert.lookupLength, query.fields = tables cert.configuration group index.val := by
  cases cert with
  | unifiedCached input arguments =>
    obtain ⟨index, same⟩ := UnifiedRowNative.UnifiedCached.source_member_with
      (fun group index => tables .unifiedCached group index.val) input arguments group query member enabled
    exact ⟨index, same⟩

end UnifiedExecution

end Airbender.Compiler
