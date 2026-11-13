module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedFoundation
public import Proven.GKRProtocol.FullArithmeticNative.BigintCachedNumericCertificate
public import Proven.Import.GKRProtocol.FullArithmeticCheckImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BigintCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

certify_full_compiler_arithmetic native inputs 276 variables 323 sources 135 gates 182 using numericFullChecked

finalize_checked_full_compiler_arithmetic native inputs 276 variables 323

end Airbender.Compiler.FullArithmeticNative.BigintCached
