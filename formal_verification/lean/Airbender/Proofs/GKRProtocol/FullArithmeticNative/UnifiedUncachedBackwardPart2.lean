import Airbender.Proofs.GKRProtocol.FullArithmeticNative.UnifiedUncachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 145 variables 149 sources 129 gates 133 phase 2 start 64 stop 96

end Airbender.Compiler.FullArithmeticNative.UnifiedUncached
