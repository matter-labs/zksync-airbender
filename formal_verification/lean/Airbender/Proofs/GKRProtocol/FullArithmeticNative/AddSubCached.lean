import Airbender.Proofs.GKRProtocol.FullArithmeticNative.AddSubCachedFoundation
import Airbender.Import.GKRProtocol.FullArithmeticCheckImport

namespace Airbender.Compiler.FullArithmeticNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

certify_full_compiler_arithmetic native inputs 48 variables 58 sources 30 gates 40

finalize_checked_full_compiler_arithmetic native inputs 48 variables 58

end Airbender.Compiler.FullArithmeticNative.AddSubCached
