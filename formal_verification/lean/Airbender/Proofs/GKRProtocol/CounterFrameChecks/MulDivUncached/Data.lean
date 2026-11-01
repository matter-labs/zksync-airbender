import Airbender.Proofs.GKRProtocol.CounterFrameChecks.MulDivUncached.Inputs
import Airbender.Import.GKRProtocol.NumericCounterFrameImport

namespace Airbender.Compiler.CounterFrameChecks.MulDivUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_counter_frame_capture data := NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.MulDivUncached.native.multiplicityColumns [23, 21, 22] Airbender.Compiler.CounterFrameNative.MulDivUncached.native.slots Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.artifact.source (Airbender.Compiler.HelperNative.MulDivUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.MulDivUncached
