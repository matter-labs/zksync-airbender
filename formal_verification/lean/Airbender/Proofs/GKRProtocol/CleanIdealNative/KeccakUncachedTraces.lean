import Airbender.Import.GKRProtocol.NumericTraceDataImport

namespace Airbender.Compiler.CleanIdealNative.KeccakUncached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
packed_normalization_rows traceRows from "artifacts/compiler/numeric-clean/keccak-uncached.json" ["normalizationTraces"]
end Airbender.Compiler.CleanIdealNative.KeccakUncached
