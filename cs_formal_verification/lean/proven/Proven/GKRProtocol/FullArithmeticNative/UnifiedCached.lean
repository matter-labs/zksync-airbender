module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.UnifiedCachedFoundation
public import Proven.GKRProtocol.FullArithmeticNative.UnifiedCachedNumericCertificate
public import Proven.Import.GKRProtocol.FullArithmeticCheckImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.UnifiedCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

certify_full_compiler_arithmetic native inputs 137 variables 147 sources 120 gates 130 using numericFullChecked

finalize_checked_full_compiler_arithmetic native inputs 137 variables 147

end Airbender.Compiler.FullArithmeticNative.UnifiedCached
