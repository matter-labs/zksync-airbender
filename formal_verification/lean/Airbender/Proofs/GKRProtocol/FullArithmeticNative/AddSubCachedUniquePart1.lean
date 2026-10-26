import Airbender.Proofs.GKRProtocol.FullArithmeticNative.AddSubCachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 48 variables 58 sources 30 gates 40 phase 0 start 32 stop 58

end Airbender.Compiler.FullArithmeticNative.AddSubCached
