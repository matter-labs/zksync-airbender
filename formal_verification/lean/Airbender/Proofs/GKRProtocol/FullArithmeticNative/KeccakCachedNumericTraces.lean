import Airbender.Import.GKRProtocol.NumericTraceDataImport

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

packed_normalization_rows numericTraceRows from "artifacts/compiler/numeric-arithmetic/keccak-cached.json" ["normalizationTraces"]

end Airbender.Compiler.FullArithmeticNative.KeccakCached
