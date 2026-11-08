import Tests.DelegationCaller
import Tests.DelegationMemory
import Slop.KernelRfl
import Slop.Trace.InitialImage

namespace Tests.DelegationRequestTrace
open Airbender Delegation Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

end Tests.DelegationRequestTrace
