import Airbender.Proofs.GKRProtocol.FullArithmeticNative.MulDivUncachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 71 variables 75 sources 43 gates 47 phase 1 start 32 stop 47

end Airbender.Compiler.FullArithmeticNative.MulDivUncached
