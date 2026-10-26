import Airbender.Import.GKRProtocol.MaterializedImport
import Airbender.Proofs.GKRProtocol.TableNative.BlakeGCached
import Airbender.Data.GKRSetup.BlakeG

namespace Airbender.Compiler.MaterializedNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_materialized_setup native from "artifacts/compiler/blake-g-cached.json"
  uncached "artifacts/compiler/blake-g-uncached.json"
  setup_model Airbender.Data.GKRSetup.BlakeG
  table_model Airbender.Compiler.TableNative.BlakeGCached.native width 9

end Airbender.Compiler.MaterializedNative.BlakeGCached
