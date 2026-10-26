import Airbender.Proofs.GKRProtocol.FullArithmeticNative.BlakeGUncachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 112 variables 116 sources 32 gates 36 phase 0 start 64 stop 96

end Airbender.Compiler.FullArithmeticNative.BlakeGUncached
