module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.NumericTraceDataImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

packed_normalization_rows numericTraceRows from "artifacts/compiler/numeric-arithmetic/keccak-cached.json" ["normalizationTraces"]

end Airbender.Compiler.FullArithmeticNative.KeccakCached
