import Airbender.Proofs.GKRProtocol.FullArithmeticNative.BlakeGCachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 113 variables 138 sources 34 gates 59 phase 2 start 32 stop 34

end Airbender.Compiler.FullArithmeticNative.BlakeGCached
