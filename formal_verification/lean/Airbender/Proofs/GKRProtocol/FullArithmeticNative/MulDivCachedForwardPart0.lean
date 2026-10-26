import Airbender.Proofs.GKRProtocol.FullArithmeticNative.MulDivCachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 71 variables 81 sources 43 gates 53 phase 1 start 0 stop 32

end Airbender.Compiler.FullArithmeticNative.MulDivCached
