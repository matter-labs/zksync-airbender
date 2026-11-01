import Airbender.Proofs.GKRProtocol.CounterFrameChecks.ShiftBinopCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.CounterFrameChecks.ShiftBinopCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding source_binding : data = NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.ShiftBinopCached.native.multiplicityColumns [27, 25, 26] Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native.slots Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.inputBank Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.source (Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.ShiftBinopCached
