import Airbender.Proofs.GKRProtocol.HistoryErasureChecks.KeccakCached.Inputs
import Airbender.Import.GKRProtocol.NumericHistoryErasureImport

namespace Airbender.Compiler.HistoryErasureChecks.KeccakCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_history_erasure_capture data := NumericHistoryErasureChecks.ofSource Airbender.Compiler.HistoryErasureNative.KeccakCached.native.historyCells Airbender.Compiler.SourceContractNative.KeccakCached.native.originals Airbender.Compiler.SourceContractNative.KeccakCached.native.clock Airbender.Compiler.FullArithmeticNative.KeccakCached.native.helperPlacement (Airbender.Compiler.HistoryErasureNative.KeccakCached.native.protectedFields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.KeccakCached.native.helperPlacement.memory))

end Airbender.Compiler.HistoryErasureChecks.KeccakCached
