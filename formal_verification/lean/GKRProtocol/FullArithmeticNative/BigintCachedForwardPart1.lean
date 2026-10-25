import GKRProtocol.FullArithmeticNative.BigintCachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 277 variables 324 sources 136 gates 183 phase 1 start 32 stop 64

end Airbender.Compiler.FullArithmeticNative.BigintCached
