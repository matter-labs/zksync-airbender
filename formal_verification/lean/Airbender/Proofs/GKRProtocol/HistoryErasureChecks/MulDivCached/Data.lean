import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.MulDivCached.Inputs
import Airbender.Import.GKRProtocol.NumericHistoryErasureImport

namespace Airbender.Compiler.HistoryErasureChecks.MulDivCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_history_erasure_capture data := NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.MulDivCached.native.historyCells Airbender.Compiler.SourceContractNative.MulDivCached.native.originals Airbender.Compiler.SourceContractNative.MulDivCached.native.clock Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.MulDivCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement.memory))

end Airbender.Compiler.HistoryErasureChecks.MulDivCached
