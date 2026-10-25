import GKRProtocol.MaterializedImport
import GKRProtocol.TableNative.JumpBranchUncached
import Airbender.Data.GKRSetup.JumpBranch

namespace Airbender.Compiler.MaterializedNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_materialized_setup native from "artifacts/compiler/jump-branch-uncached.json"
  uncached "artifacts/compiler/jump-branch-uncached.json"
  setup_model Airbender.Data.GKRSetup.JumpBranch
  table_model Airbender.Compiler.TableNative.JumpBranchUncached.native width 10

end Airbender.Compiler.MaterializedNative.JumpBranchUncached
