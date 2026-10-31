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

end PooledExecution

namespace UnifiedExecution

/-- The physical native input proves the execute bit for either cache mode. -/
theorem ProgramLogicalRowCertificate.row_active {tables : ProgramLookupRows}
    (cert : ProgramLogicalRowCertificate tables) :
    cert.row.assignment cert.row.columns.execute = 1 := by
  cases cert with
  | unifiedUncached input _arguments => exact UnifiedRowNative.UnifiedUncached.input_active input
  | unifiedCached input _arguments => exact UnifiedRowNative.UnifiedCached.input_active input

end UnifiedExecution

end Airbender.Compiler
