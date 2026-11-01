import Airbender.Proofs.GKRProtocol.CounterFrameChecks.AddSubUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.CounterFrameChecks.AddSubUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding source_binding : data = NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.AddSubUncached.native.multiplicityColumns [21, 19, 20] Airbender.Compiler.CounterFrameNative.AddSubUncached.native.slots Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.artifact.source (Airbender.Compiler.HelperNative.AddSubUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.AddSubUncached
