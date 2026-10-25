import GKRProtocol.FunctionalNative.WordMemoryUncachedFoundation

namespace Airbender.Compiler.FunctionalNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_functional_graph native phase 0 start 32 stop 33

end Airbender.Compiler.FunctionalNative.WordMemoryUncached
