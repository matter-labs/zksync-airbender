module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FullArithmeticNative.SubwordMemoryCachedFoundation
public import Proven.GKRProtocol.FullArithmeticNative.SubwordMemoryCachedNumericCertificate
public import Proven.Import.GKRProtocol.FullArithmeticCheckImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

certify_full_compiler_arithmetic native inputs 68 variables 77 sources 43 gates 52 using numericFullChecked

finalize_checked_full_compiler_arithmetic native inputs 68 variables 77

end Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached
