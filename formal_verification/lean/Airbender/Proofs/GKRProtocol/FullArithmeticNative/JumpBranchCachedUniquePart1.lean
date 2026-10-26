import Airbender.Proofs.GKRProtocol.FullArithmeticNative.JumpBranchCachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 55 variables 65 sources 26 gates 36 phase 0 start 32 stop 64

end Airbender.Compiler.FullArithmeticNative.JumpBranchCached
