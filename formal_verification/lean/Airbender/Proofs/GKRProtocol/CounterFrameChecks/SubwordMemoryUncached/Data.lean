import Airbender.Proofs.GKRProtocol.CounterFrameChecks.SubwordMemoryUncached.Inputs
import Airbender.Import.GKRProtocol.NumericCounterFrameImport

namespace Airbender.Compiler.CounterFrameChecks.SubwordMemoryUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_counter_frame_capture data := NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.SubwordMemoryUncached.native.multiplicityColumns [16, 14, 15] Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native.slots Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.source (Airbender.Compiler.HelperNative.SubwordMemoryUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.SubwordMemoryUncached
