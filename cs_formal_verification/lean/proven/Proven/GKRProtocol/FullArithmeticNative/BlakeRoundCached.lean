module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation
public import Proven.GKRProtocol.FullArithmeticNative.BlakeRoundCachedNumericCertificate
public import Proven.Import.GKRProtocol.FullArithmeticCheckImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

certify_full_compiler_arithmetic native inputs 763 variables 858 sources 220 gates 315 using numericFullChecked

finalize_checked_full_compiler_arithmetic native inputs 763 variables 858

end Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
