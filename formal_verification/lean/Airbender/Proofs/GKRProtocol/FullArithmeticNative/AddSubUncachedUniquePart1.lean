import Airbender.Proofs.GKRProtocol.FullArithmeticNative.AddSubUncachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 48 variables 52 sources 30 gates 34 phase 0 start 32 stop 52

end Airbender.Compiler.FullArithmeticNative.AddSubUncached
