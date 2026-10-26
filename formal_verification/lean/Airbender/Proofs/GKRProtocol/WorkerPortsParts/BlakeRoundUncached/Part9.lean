import Airbender.Proofs.GKRProtocol.WorkerPortsParts.BlakeRoundUncached.Shared
import Airbender.Import.GKRProtocol.WorkerPortsChecks

namespace Airbender.Compiler.WorkerPortsNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

worker_checks_part historyPart36 input_list (List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size)
  test_fn historyPredicate start 36 stop 40

end Airbender.Compiler.WorkerPortsNative.BlakeRoundUncached
