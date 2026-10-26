import Airbender.Proofs.GKRProtocol.FullArithmeticNative.SubwordMemoryCachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 68 variables 77 sources 43 gates 52 phase 0 start 64 stop 77

end Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached
