import GKRProtocol.FullArithmeticNative.KeccakUncachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 267 variables 272 sources 192 gates 197 phase 1 start 64 stop 96

end Airbender.Compiler.FullArithmeticNative.KeccakUncached
