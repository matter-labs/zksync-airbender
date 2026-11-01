import Airbender.Proofs.GKRProtocol.CounterFrameChecks.UnifiedUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.CounterFrameChecks.UnifiedUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding source_binding : data = NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.UnifiedUncached.native.multiplicityColumns [57, 55, 56] Airbender.Compiler.CounterFrameNative.UnifiedUncached.native.slots Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.artifact.source (Airbender.Compiler.HelperNative.UnifiedUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.UnifiedUncached
