import Airbender.Proofs.GKRProtocol.CounterFrameChecks.BlakeRoundUncached.Data
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.CounterFrameChecks.BlakeRoundUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding source_binding : data = NumericCounterFrameChecks.ofTyped Airbender.Compiler.TableNative.BlakeRoundUncached.native.multiplicityColumns [537, 536] Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native.slots Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.artifact.source (Airbender.Compiler.HelperNative.BlakeRoundUncached.native.fields.map (fun field => field.polynomial Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.helperPlacement))

end Airbender.Compiler.CounterFrameChecks.BlakeRoundUncached
