import Airbender.Proofs.GKRProtocol.FunctionalNative.AddSubUncachedFoundation

namespace Airbender.Compiler.FunctionalNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_functional_graph native phase 1 start 0 stop 4

end Airbender.Compiler.FunctionalNative.AddSubUncached
