module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.JumpBranchCachedFoundation
public import Proven.GKRProtocol.FullArithmeticNative.JumpBranchCachedNumericCertificate
public import Proven.Import.GKRProtocol.FullArithmeticCheckImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

certify_full_compiler_arithmetic native inputs 55 variables 65 sources 26 gates 36 using numericFullChecked

finalize_checked_full_compiler_arithmetic native inputs 55 variables 65

end Airbender.Compiler.FullArithmeticNative.JumpBranchCached
