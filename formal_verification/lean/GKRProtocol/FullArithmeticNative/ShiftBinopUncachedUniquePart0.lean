import GKRProtocol.FullArithmeticNative.ShiftBinopUncachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 98 variables 102 sources 52 gates 56 phase 0 start 0 stop 32

end Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached
