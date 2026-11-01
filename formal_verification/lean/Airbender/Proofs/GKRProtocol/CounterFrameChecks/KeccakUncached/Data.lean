import Airbender.Proofs.GKRProtocol.CounterFrameChecks.KeccakUncached.Inputs
import Airbender.Import.GKRProtocol.NumericCounterFrameImport

namespace Airbender.Compiler.CounterFrameChecks.KeccakUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_counter_frame_capture data := NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.KeccakUncached.native.multiplicityColumns [174, 173] Airbender.Compiler.CounterFrameNative.KeccakUncached.native.slots Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.artifact.source (Airbender.Compiler.HelperNative.KeccakUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.KeccakUncached
