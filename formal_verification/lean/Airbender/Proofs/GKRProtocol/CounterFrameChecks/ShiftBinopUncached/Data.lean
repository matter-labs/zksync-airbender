import Airbender.Proofs.GKRProtocol.CounterFrameChecks.ShiftBinopUncached.Inputs
import Airbender.Import.GKRProtocol.NumericCounterFrameImport

namespace Airbender.Compiler.CounterFrameChecks.ShiftBinopUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_counter_frame_capture data := NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.ShiftBinopUncached.native.multiplicityColumns [27, 25, 26] Airbender.Compiler.CounterFrameNative.ShiftBinopUncached.native.slots Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.artifact.source (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.ShiftBinopUncached
