import GKRProtocol.MaterializedImport
import GKRProtocol.TableNative.BlakeGUncached
import Airbender.Data.GKRSetup.BlakeG

namespace Airbender.Compiler.MaterializedNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_materialized_setup native from "artifacts/compiler/blake-g-uncached.json"
  uncached "artifacts/compiler/blake-g-uncached.json"
  setup_model Airbender.Data.GKRSetup.BlakeG
  table_model Airbender.Compiler.TableNative.BlakeGUncached.native width 9

end Airbender.Compiler.MaterializedNative.BlakeGUncached
