import Airbender.Proofs.GKRProtocol.CounterFrameChecks.BlakeRoundCached.Inputs
import Airbender.Import.GKRProtocol.NumericCounterFrameImport

namespace Airbender.Compiler.CounterFrameChecks.BlakeRoundCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_counter_frame_capture data := NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.BlakeRoundCached.native.multiplicityColumns [537, 536] Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native.slots Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.source (Airbender.Compiler.HelperNative.BlakeRoundCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.BlakeRoundCached
