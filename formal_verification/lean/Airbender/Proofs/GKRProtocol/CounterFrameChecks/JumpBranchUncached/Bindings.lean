import Airbender.Proofs.GKRProtocol.CounterFrameChecks.JumpBranchUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.CounterFrameChecks.JumpBranchUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding source_binding : data = NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.JumpBranchUncached.native.multiplicityColumns [28, 26, 27] Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native.slots Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.source (Airbender.Compiler.HelperNative.JumpBranchUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.JumpBranchUncached
