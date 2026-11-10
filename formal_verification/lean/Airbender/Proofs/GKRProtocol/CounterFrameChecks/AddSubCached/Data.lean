import Airbender.Proofs.GKRProtocol.CounterFrameChecks.AddSubCached.Inputs
import Airbender.Import.GKRProtocol.NumericCounterFrameImport

namespace Airbender.Compiler.CounterFrameChecks.AddSubCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_counter_frame_capture data := NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.AddSubCached.native.multiplicityColumns [21, 19, 20] Airbender.Compiler.CounterFrameNative.AddSubCached.native.slots Airbender.Compiler.FullArithmeticNative.AddSubCached.native.inputBank Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.source (Airbender.Compiler.HelperNative.AddSubCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.AddSubCached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.AddSubCached
