import Airbender.Proofs.GKRProtocol.FullArithmeticNative.BlakeRoundCachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 763 variables 858 sources 220 gates 315 phase 0 start 608 stop 640

end Airbender.Compiler.FullArithmeticNative.BlakeRoundCached
