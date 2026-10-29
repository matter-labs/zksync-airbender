import Airbender.Proofs.GKRProtocol.FullArithmeticNative.BigintCachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 276 variables 323 sources 135 gates 182 phase 1 start 0 stop 32

end Airbender.Compiler.FullArithmeticNative.BigintCached
