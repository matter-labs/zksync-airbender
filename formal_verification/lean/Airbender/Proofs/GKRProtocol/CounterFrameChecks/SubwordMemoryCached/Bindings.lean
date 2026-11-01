import Airbender.Proofs.GKRProtocol.CounterFrameChecks.SubwordMemoryCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.CounterFrameChecks.SubwordMemoryCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding source_binding : data = NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.SubwordMemoryCached.native.multiplicityColumns [16, 14, 15] Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native.slots Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.source (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.SubwordMemoryCached
