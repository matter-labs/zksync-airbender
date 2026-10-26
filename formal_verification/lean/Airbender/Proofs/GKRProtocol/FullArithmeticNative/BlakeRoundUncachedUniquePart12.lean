import Airbender.Proofs.GKRProtocol.FullArithmeticNative.BlakeRoundUncachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 763 variables 769 sources 220 gates 226 phase 0 start 384 stop 416

end Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached
