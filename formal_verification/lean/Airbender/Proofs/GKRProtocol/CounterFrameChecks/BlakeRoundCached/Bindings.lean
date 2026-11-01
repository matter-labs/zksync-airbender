import Airbender.Proofs.GKRProtocol.CounterFrameChecks.BlakeRoundCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.CounterFrameChecks.BlakeRoundCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding source_binding : data = NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns [537, 536] Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.slots Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.source (Airbender.Compiler.HelperNative.BlakeRoundCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.BlakeRoundCached
