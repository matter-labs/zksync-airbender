import Airbender.Proofs.GKRProtocol.FullArithmeticNative.UnifiedUncachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 137 variables 141 sources 120 gates 124 phase 0 start 128 stop 141

end Airbender.Compiler.FullArithmeticNative.UnifiedUncached
