import GKRProtocol.FullArithmeticNative.ShiftBinopCachedFoundation

namespace Airbender.Compiler.FullArithmeticNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_full_compiler_arithmetic native inputs 98 variables 108 sources 52 gates 62 phase 2 start 0 stop 32

end Airbender.Compiler.FullArithmeticNative.ShiftBinopCached
