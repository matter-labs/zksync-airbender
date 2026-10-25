import GKRProtocol.FullArithmeticNative.WordMemoryCachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 52 variables 63 sources 27 gates 38 phase 2 start 0 stop 27

end Airbender.Compiler.FullArithmeticNative.WordMemoryCached
