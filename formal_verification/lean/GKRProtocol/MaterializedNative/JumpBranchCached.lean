import GKRProtocol.MaterializedImport
import GKRProtocol.TableNative.JumpBranchCached
import Airbender.Data.GKRSetup.JumpBranch

namespace Airbender.Compiler.MaterializedNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_materialized_setup native from "artifacts/compiler/jump-branch-cached.json"
  uncached "artifacts/compiler/jump-branch-uncached.json"
  setup_model Airbender.Data.GKRSetup.JumpBranch
  table_model Airbender.Compiler.TableNative.JumpBranchCached.native width 10

end Airbender.Compiler.MaterializedNative.JumpBranchCached
