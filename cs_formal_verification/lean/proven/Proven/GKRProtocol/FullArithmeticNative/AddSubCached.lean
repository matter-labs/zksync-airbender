module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.AddSubCachedFoundation
public import Proven.Import.GKRProtocol.FullArithmeticCheckImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.AddSubCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

certify_full_compiler_arithmetic native inputs 48 variables 58 sources 30 gates 40

finalize_checked_full_compiler_arithmetic native inputs 48 variables 58

end Airbender.Compiler.FullArithmeticNative.AddSubCached
