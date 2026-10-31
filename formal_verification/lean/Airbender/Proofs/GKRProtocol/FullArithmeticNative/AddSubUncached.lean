import Airbender.Proofs.GKRProtocol.FullArithmeticNative.AddSubUncachedFoundation
import Airbender.Import.GKRProtocol.FullArithmeticCheckImport

namespace Airbender.Compiler.FullArithmeticNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

certify_full_compiler_arithmetic native inputs 48 variables 52 sources 30 gates 34

finalize_full_compiler_arithmetic native inputs 48 variables 52 sources 30 gates 34

end Airbender.Compiler.FullArithmeticNative.AddSubUncached
