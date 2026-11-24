module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.WordMemoryCachedFoundation
public import Proven.GKRProtocol.FullArithmeticNative.WordMemoryCachedNumericCertificate
public import Proven.Import.GKRProtocol.FullArithmeticCheckImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

certify_full_compiler_arithmetic native inputs 52 variables 63 sources 27 gates 38 using numericFullChecked

finalize_checked_full_compiler_arithmetic native inputs 52 variables 63

end Airbender.Compiler.FullArithmeticNative.WordMemoryCached
