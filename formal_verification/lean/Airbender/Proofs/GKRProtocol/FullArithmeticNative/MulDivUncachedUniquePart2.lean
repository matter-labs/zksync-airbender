import Airbender.Proofs.GKRProtocol.FullArithmeticNative.MulDivUncachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 71 variables 75 sources 43 gates 47 phase 0 start 64 stop 75

end Airbender.Compiler.FullArithmeticNative.MulDivUncached
