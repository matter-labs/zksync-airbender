import Airbender.Import.GKRProtocol.MaterializedImport
import Airbender.Proofs.GKRProtocol.TableNative.AddSubUncached
import Airbender.Data.GKRSetup.AddSub

namespace Airbender.Compiler.MaterializedNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_materialized_setup native from "artifacts/compiler/add-sub-uncached.json"
  uncached "artifacts/compiler/add-sub-uncached.json"
  setup_model Airbender.Data.GKRSetup.AddSub
  table_model Airbender.Compiler.TableNative.AddSubUncached.native width 8

end Airbender.Compiler.MaterializedNative.AddSubUncached
