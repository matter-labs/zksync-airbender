module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCachedNumericCertificate
public import Proven.Import.GKRProtocol.FullArithmeticCheckImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

certify_full_compiler_arithmetic native inputs 266 variables 301 sources 187 gates 222 using numericFullChecked

finalize_checked_full_compiler_arithmetic native inputs 266 variables 301

end Airbender.Compiler.FullArithmeticNative.KeccakCached
