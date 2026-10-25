import GKRProtocol.MaterializedImport
import GKRProtocol.TableNative.UnifiedUncached
import Airbender.Data.GKRSetup.Unified

namespace Airbender.Compiler.MaterializedNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_materialized_setup native from "artifacts/compiler/unified-uncached.json"
  uncached "artifacts/compiler/unified-uncached.json"
  setup_model Airbender.Data.GKRSetup.Unified
  table_model Airbender.Compiler.TableNative.UnifiedUncached.native width 10

end Airbender.Compiler.MaterializedNative.UnifiedUncached
