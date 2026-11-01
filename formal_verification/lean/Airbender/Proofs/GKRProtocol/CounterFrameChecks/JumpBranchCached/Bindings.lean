import Airbender.Proofs.GKRProtocol.CounterFrameChecks.JumpBranchCached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.CounterFrameChecks.JumpBranchCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding source_binding : data = NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.JumpBranchCached.native.multiplicityColumns [28, 26, 27] Airbender.Compiler.CounterFrameNative.JumpBranchCached.native.slots Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.inputBank Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.source (Airbender.Compiler.HelperNative.JumpBranchCached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.JumpBranchCached
