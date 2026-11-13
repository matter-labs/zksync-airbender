module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.MulDivCachedFoundation
public import Proven.GKRProtocol.FullArithmeticNative.MulDivCachedNumericCertificate
public import Proven.Import.GKRProtocol.FullArithmeticCheckImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.MulDivCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

certify_full_compiler_arithmetic native inputs 71 variables 81 sources 43 gates 53 using numericFullChecked

finalize_checked_full_compiler_arithmetic native inputs 71 variables 81

end Airbender.Compiler.FullArithmeticNative.MulDivCached
