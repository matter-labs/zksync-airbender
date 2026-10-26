import Airbender.Proofs.GKRProtocol.FullArithmeticNative.JumpBranchUncachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 55 variables 59 sources 26 gates 30 phase 0 start 32 stop 59

end Airbender.Compiler.FullArithmeticNative.JumpBranchUncached
