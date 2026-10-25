import GKRProtocol.FullArithmeticNative.BigintUncachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 277 variables 283 sources 136 gates 142 phase 0 start 128 stop 160

end Airbender.Compiler.FullArithmeticNative.BigintUncached
