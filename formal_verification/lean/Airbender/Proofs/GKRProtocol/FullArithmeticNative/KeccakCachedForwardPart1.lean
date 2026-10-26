import Airbender.Proofs.GKRProtocol.FullArithmeticNative.KeccakCachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 267 variables 302 sources 192 gates 227 phase 1 start 32 stop 64

end Airbender.Compiler.FullArithmeticNative.KeccakCached
