import GKRProtocol.MaterializedImport
import GKRProtocol.TableNative.BigintUncached
import Airbender.Data.GKRSetup.Bigint

namespace Airbender.Compiler.MaterializedNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_materialized_setup native from "artifacts/compiler/bigint-uncached.json"
  uncached "artifacts/compiler/bigint-uncached.json"
  setup_model Airbender.Data.GKRSetup.Bigint
  table_model Airbender.Compiler.TableNative.BigintUncached.native width 3

end Airbender.Compiler.MaterializedNative.BigintUncached
