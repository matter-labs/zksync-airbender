import Airbender.Proofs.GKRProtocol.CounterFrameChecks.BigintCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.CounterFrameChecks.BigintCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding source_binding : data = NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.BigintCached.native.multiplicityColumns [159, 157, 158] Airbender.Compiler.CounterFrameNative.BigintCached.native.slots Airbender.Compiler.FullArithmeticNative.BigintCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.source (Airbender.Compiler.HelperNative.BigintCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BigintCached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.BigintCached
