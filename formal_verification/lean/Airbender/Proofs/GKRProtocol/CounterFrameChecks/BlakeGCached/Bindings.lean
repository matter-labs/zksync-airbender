import Airbender.Proofs.GKRProtocol.CounterFrameChecks.BlakeGCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.CounterFrameChecks.BlakeGCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding source_binding : data = NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.BlakeGCached.native.multiplicityColumns [56, 55] Airbender.Compiler.CounterFrameNative.BlakeGCached.native.slots Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.source (Airbender.Compiler.HelperNative.BlakeGCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.BlakeGCached
