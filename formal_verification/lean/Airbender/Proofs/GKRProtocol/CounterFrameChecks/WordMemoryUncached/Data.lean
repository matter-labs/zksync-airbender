import Airbender.Proofs.GKRProtocol.CounterFrameChecks.WordMemoryUncached.Inputs
import Airbender.Import.GKRProtocol.NumericCounterFrameImport

namespace Airbender.Compiler.CounterFrameChecks.WordMemoryUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_counter_frame_capture data := NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.WordMemoryUncached.native.multiplicityColumns [10, 8, 9] Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native.slots Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.artifact.source (Airbender.Compiler.HelperNative.WordMemoryUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.WordMemoryUncached
