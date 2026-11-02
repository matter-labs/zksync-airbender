import Airbender.Proofs.GKRProtocol.WorkerPortChecks.BlakeRoundUncached.Bindings

namespace Airbender.Compiler.WorkerPortChecks.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericWorkerPortChecks.check data = true := by decide +kernel

theorem originalChecked : original.check = true :=
  NumericWorkerPortChecks.check_sound original data source_binding checked

def facts := original_check originalChecked

end Airbender.Compiler.WorkerPortChecks.BlakeRoundUncached
