import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.AddSubCached.Inputs
import Airbender.Import.GKRProtocol.NumericHistoryErasureImport

namespace Airbender.Compiler.HistoryErasureChecks.AddSubCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_history_erasure_capture data := NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.AddSubCached.native.historyCells Airbender.Compiler.SourceContractNative.AddSubCached.native.originals Airbender.Compiler.SourceContractNative.AddSubCached.native.clock Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.AddSubCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement.memory))

end Airbender.Compiler.HistoryErasureChecks.AddSubCached
