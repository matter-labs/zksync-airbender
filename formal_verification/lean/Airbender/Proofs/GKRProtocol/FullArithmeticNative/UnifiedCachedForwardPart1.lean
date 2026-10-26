import Airbender.Proofs.GKRProtocol.FullArithmeticNative.UnifiedCachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 145 variables 155 sources 129 gates 139 phase 1 start 32 stop 64

end Airbender.Compiler.FullArithmeticNative.UnifiedCached
