import GKRProtocol.FunctionalNative.BlakeGCachedFoundation

namespace Airbender.Compiler.FunctionalNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

check_functional_graph native phase 0 start 96 stop 112

end Airbender.Compiler.FunctionalNative.BlakeGCached
