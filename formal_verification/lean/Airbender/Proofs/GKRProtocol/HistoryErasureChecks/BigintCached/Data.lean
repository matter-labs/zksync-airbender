import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.BigintCached.Inputs
import Airbender.Import.GKRProtocol.NumericHistoryErasureImport

namespace Airbender.Compiler.HistoryErasureChecks.BigintCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_history_erasure_capture data := NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.BigintCached.native.historyCells Airbender.Compiler.SourceContractNative.BigintCached.native.originals Airbender.Compiler.SourceContractNative.BigintCached.native.clock Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.BigintCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement.memory))

end Airbender.Compiler.HistoryErasureChecks.BigintCached
