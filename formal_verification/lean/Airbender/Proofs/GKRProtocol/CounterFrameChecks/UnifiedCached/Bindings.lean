import Airbender.Proofs.GKRProtocol.CounterFrameChecks.UnifiedCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.CounterFrameChecks.UnifiedCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding source_binding : data = NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.UnifiedCached.native.multiplicityColumns [57, 55, 56] Airbender.Compiler.CounterFrameNative.UnifiedCached.native.slots Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.inputBank Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.source (Airbender.Compiler.HelperNative.UnifiedCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.UnifiedCached
