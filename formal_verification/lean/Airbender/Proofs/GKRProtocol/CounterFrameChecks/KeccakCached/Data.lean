import Airbender.Proofs.GKRProtocol.CounterFrameChecks.KeccakCached.Inputs
import Airbender.Import.GKRProtocol.NumericCounterFrameImport

namespace Airbender.Compiler.CounterFrameChecks.KeccakCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_counter_frame_capture data := NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.KeccakCached.native.multiplicityColumns [174, 173] Airbender.Compiler.CounterFrameNative.KeccakCached.native.slots Airbender.Compiler.FullArithmeticNative.KeccakCached.native.inputBank Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.source (Airbender.Compiler.HelperNative.KeccakCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.KeccakCached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.KeccakCached
