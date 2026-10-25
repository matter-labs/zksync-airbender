import GKRProtocol.FunctionalNative.BigintCachedFoundation

namespace Airbender.Compiler.FunctionalNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_functional_graph native phase 1 start 32 stop 49

end Airbender.Compiler.FunctionalNative.BigintCached
