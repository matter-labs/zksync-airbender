import Airbender.Proofs.GKRProtocol.FullArithmeticNative.BigintUncachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 276 variables 282 sources 135 gates 141 phase 0 start 160 stop 192

end Airbender.Compiler.FullArithmeticNative.BigintUncached
