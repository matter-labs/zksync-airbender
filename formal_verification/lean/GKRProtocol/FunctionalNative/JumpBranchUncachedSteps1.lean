import GKRProtocol.FunctionalNative.JumpBranchUncachedFoundation

namespace Airbender.Compiler.FunctionalNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_functional_graph native phase 0 start 32 stop 39

end Airbender.Compiler.FunctionalNative.JumpBranchUncached
