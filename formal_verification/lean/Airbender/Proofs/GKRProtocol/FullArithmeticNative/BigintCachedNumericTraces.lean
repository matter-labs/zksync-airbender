import Airbender.Import.GKRProtocol.NumericTraceDataImport

namespace Airbender.Compiler.FullArithmeticNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

packed_normalization_rows numericTraceRows from "artifacts/compiler/numeric-arithmetic/bigint-cached.json" ["normalizationTraces"]

end Airbender.Compiler.FullArithmeticNative.BigintCached
