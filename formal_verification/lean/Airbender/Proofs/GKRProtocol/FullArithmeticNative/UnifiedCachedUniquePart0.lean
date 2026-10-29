import Airbender.Proofs.GKRProtocol.FullArithmeticNative.UnifiedCachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 137 variables 147 sources 120 gates 130 phase 0 start 0 stop 32

end Airbender.Compiler.FullArithmeticNative.UnifiedCached
