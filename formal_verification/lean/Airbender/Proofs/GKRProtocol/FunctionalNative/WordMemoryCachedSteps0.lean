import Airbender.Proofs.GKRProtocol.FunctionalNative.WordMemoryCachedFoundation

namespace Airbender.Compiler.FunctionalNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_functional_graph native phase 0 start 0 stop 32

end Airbender.Compiler.FunctionalNative.WordMemoryCached
