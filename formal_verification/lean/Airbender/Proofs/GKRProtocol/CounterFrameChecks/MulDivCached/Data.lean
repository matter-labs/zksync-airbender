import Airbender.Proofs.GKRProtocol.CounterFrameChecks.MulDivCached.Inputs
import Airbender.Import.GKRProtocol.NumericCounterFrameImport

namespace Airbender.Compiler.CounterFrameChecks.MulDivCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_counter_frame_capture data := NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.MulDivCached.native.multiplicityColumns [23, 21, 22] Airbender.Compiler.CounterFrameNative.MulDivCached.native.slots Airbender.Compiler.FullArithmeticNative.MulDivCached.native.inputBank Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.source (Airbender.Compiler.HelperNative.MulDivCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.MulDivCached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.MulDivCached
