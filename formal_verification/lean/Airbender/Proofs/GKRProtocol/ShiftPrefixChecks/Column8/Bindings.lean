import Airbender.Proofs.GKRProtocol.ShiftPrefixChecks.Column8.Codes
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.ShiftPrefixChecks.Column8
open Airbender Airbender.Compiler
open PackedSetupEquality PackedSetupNormalization
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

numeric_data_binding source0_binding : Airbender.Compiler.ShiftPrefixNative.Column8.original0 = source0.map BlockCode.decode
numeric_data_binding target0_binding : Airbender.Compiler.ShiftPrefixNative.Column8.target0 = (target0Region0 ++ target0Region1 ++ target0Region2 ++ target0Region3 ++ target0Region4 ++ target0Region5 ++ target0Region6).map BlockCode.decode
numeric_data_binding target0Region0_binding : Airbender.Compiler.ShiftPrefixNative.Column8.target0Region0 = target0Region0.map BlockCode.decode
numeric_data_binding target0Region1_binding : Airbender.Compiler.ShiftPrefixNative.Column8.target0Region1 = target0Region1.map BlockCode.decode
numeric_data_binding target0Region2_binding : Airbender.Compiler.ShiftPrefixNative.Column8.target0Region2 = target0Region2.map BlockCode.decode
numeric_data_binding target0Region3_binding : Airbender.Compiler.ShiftPrefixNative.Column8.target0Region3 = target0Region3.map BlockCode.decode
numeric_data_binding target0Region4_binding : Airbender.Compiler.ShiftPrefixNative.Column8.target0Region4 = target0Region4.map BlockCode.decode
numeric_data_binding target0Region5_binding : Airbender.Compiler.ShiftPrefixNative.Column8.target0Region5 = target0Region5.map BlockCode.decode
numeric_data_binding target0Region6_binding : Airbender.Compiler.ShiftPrefixNative.Column8.target0Region6 = target0Region6.map BlockCode.decode

end Airbender.Compiler.ShiftPrefixChecks.Column8
