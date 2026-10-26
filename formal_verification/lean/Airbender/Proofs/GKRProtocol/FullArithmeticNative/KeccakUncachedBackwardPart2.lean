import Airbender.Proofs.GKRProtocol.FullArithmeticNative.KeccakUncachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 266 variables 271 sources 187 gates 192 phase 2 start 64 stop 96

end Airbender.Compiler.FullArithmeticNative.KeccakUncached
