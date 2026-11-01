import Airbender.Proofs.GKRProtocol.CounterFrameChecks.BigintUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.CounterFrameChecks.BigintUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding source_binding : data = NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.BigintUncached.native.multiplicityColumns [159, 157, 158] Airbender.Compiler.CounterFrameNative.BigintUncached.native.slots Airbender.Compiler.FullArithmeticNative.BigintUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BigintUncached.native.artifact.source (Airbender.Compiler.HelperNative.BigintUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BigintUncached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.BigintUncached
