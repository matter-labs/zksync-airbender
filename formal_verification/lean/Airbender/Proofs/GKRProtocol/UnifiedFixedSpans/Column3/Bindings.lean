import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column3.Codes
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.UnifiedFixedSpans.Column3
open Airbender Airbender.Compiler
open PackedSetupEquality
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

numeric_data_binding source0_binding : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.source0 = (source0.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets0_binding : Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0.target0 = targets0.map BlockCode.decode

end Airbender.Compiler.UnifiedFixedSpans.Column3
