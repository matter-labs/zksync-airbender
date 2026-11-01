import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.BlakeGCached.Inputs
import Airbender.Import.GKRProtocol.NumericHistoryErasureImport

namespace Airbender.Compiler.HistoryErasureChecks.BlakeGCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_history_erasure_capture data := NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.BlakeGCached.native.historyCells Airbender.Compiler.SourceContractNative.BlakeGCached.native.originals Airbender.Compiler.SourceContractNative.BlakeGCached.native.clock Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.BlakeGCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.helperPlacement.memory))

end Airbender.Compiler.HistoryErasureChecks.BlakeGCached
