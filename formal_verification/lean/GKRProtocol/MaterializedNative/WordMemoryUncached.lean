import GKRProtocol.MaterializedImport
import GKRProtocol.TableNative.WordMemoryUncached
import Airbender.Data.GKRSetup.WordMemory

namespace Airbender.Compiler.MaterializedNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_materialized_setup native from "artifacts/compiler/word-memory-uncached.json"
  uncached "artifacts/compiler/word-memory-uncached.json"
  setup_model Airbender.Data.GKRSetup.WordMemory
  table_model Airbender.Compiler.TableNative.WordMemoryUncached.native width 9

end Airbender.Compiler.MaterializedNative.WordMemoryUncached
