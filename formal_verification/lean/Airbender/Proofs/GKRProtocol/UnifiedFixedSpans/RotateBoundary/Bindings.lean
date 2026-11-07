import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.RotateBoundary.Codes
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.UnifiedFixedSpans.RotateBoundary
open Airbender Airbender.Compiler
open PackedSetupEquality
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

numeric_data_binding source_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source14 = (sourceCode.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target14 = targetsCode.map BlockCode.decode

end Airbender.Compiler.UnifiedFixedSpans.RotateBoundary
