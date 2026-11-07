import Airbender.Proofs.GKRProtocol.CounterFrameChecks.WordMemoryCached.Inputs
import Airbender.Import.GKRProtocol.NumericCounterFrameImport

namespace Airbender.Compiler.CounterFrameChecks.WordMemoryCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_counter_frame_capture data := NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.WordMemoryCached.native.multiplicityColumns [10, 8, 9] Airbender.Compiler.CounterFrameNative.WordMemoryCached.native.slots Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.inputBank Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.artifact.source (Airbender.Compiler.HelperNative.WordMemoryCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.WordMemoryCached
