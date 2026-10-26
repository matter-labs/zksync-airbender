import Airbender.Proofs.GKRProtocol.FullArithmeticNative.SubwordMemoryUncachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 68 variables 71 sources 43 gates 46 phase 2 start 32 stop 43

end Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached
