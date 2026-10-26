import Airbender.Proofs.GKRProtocol.WorkerPortsParts.BlakeRoundCached.Shared
import Airbender.Import.GKRProtocol.WorkerPortsChecks

namespace Airbender.Compiler.WorkerPortsNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

worker_checks_part historyPart16 input_list (List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size)
  test_fn historyPredicate start 16 stop 20

end Airbender.Compiler.WorkerPortsNative.BlakeRoundCached
