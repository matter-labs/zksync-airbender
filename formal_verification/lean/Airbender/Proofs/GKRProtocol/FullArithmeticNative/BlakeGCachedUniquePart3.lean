import Airbender.Proofs.GKRProtocol.FullArithmeticNative.BlakeGCachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 112 variables 137 sources 32 gates 57 phase 0 start 96 stop 128

end Airbender.Compiler.FullArithmeticNative.BlakeGCached
