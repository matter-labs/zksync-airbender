import GKRProtocol.MaterializedImport
import GKRProtocol.TableNative.SubwordMemoryCached
import Airbender.Data.GKRSetup.SubwordMemory

namespace Airbender.Compiler.MaterializedNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_materialized_setup native from "artifacts/compiler/subword-memory-cached.json"
  uncached "artifacts/compiler/subword-memory-uncached.json"
  setup_model Airbender.Data.GKRSetup.SubwordMemory
  table_model Airbender.Compiler.TableNative.SubwordMemoryCached.native width 9

end Airbender.Compiler.MaterializedNative.SubwordMemoryCached
