module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.BlakeGCachedFoundation
public import Proven.GKRProtocol.FullArithmeticNative.BlakeGCachedNumericCertificate
public import Proven.Import.GKRProtocol.FullArithmeticCheckImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BlakeGCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

certify_full_compiler_arithmetic native inputs 112 variables 137 sources 32 gates 57 using numericFullChecked

finalize_checked_full_compiler_arithmetic native inputs 112 variables 137

end Airbender.Compiler.FullArithmeticNative.BlakeGCached
