import GKRProtocol.FunctionalNative.KeccakUncachedFoundation

namespace Airbender.Compiler.FunctionalNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_functional_graph native phase 0 start 64 stop 96

end Airbender.Compiler.FunctionalNative.KeccakUncached
