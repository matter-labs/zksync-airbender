import GKRProtocol.FullArithmeticNative.BlakeGUncachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 113 variables 117 sources 34 gates 38 phase 2 start 0 stop 32

end Airbender.Compiler.FullArithmeticNative.BlakeGUncached
