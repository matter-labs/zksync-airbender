import Airbender.Import.GKRProtocol.NumericTraceDataImport

namespace Airbender.Compiler.CleanIdealNative.BigintCached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
packed_normalization_rows traceRows from "artifacts/compiler/numeric-clean/bigint-cached.json" ["normalizationTraces"]
end Airbender.Compiler.CleanIdealNative.BigintCached
