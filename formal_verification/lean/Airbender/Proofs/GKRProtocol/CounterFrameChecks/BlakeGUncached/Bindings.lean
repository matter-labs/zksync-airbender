import Airbender.Proofs.GKRProtocol.CounterFrameChecks.BlakeGUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.CounterFrameChecks.BlakeGUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding source_binding : data = NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.BlakeGUncached.native.multiplicityColumns [56, 55] Airbender.Compiler.CounterFrameNative.BlakeGUncached.native.slots Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.source (Airbender.Compiler.HelperNative.BlakeGUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.BlakeGUncached
