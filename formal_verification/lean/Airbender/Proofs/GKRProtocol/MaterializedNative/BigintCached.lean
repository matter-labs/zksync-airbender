import Airbender.Import.GKRProtocol.MaterializedImport
import Airbender.Proofs.GKRProtocol.TableNative.BigintCached
import Airbender.Data.GKRSetup.Bigint

namespace Airbender.Compiler.MaterializedNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_materialized_setup native from "artifacts/compiler/bigint-cached.json"
  uncached "artifacts/compiler/bigint-uncached.json"
  setup_model Airbender.Data.GKRSetup.Bigint
  table_model Airbender.Compiler.TableNative.BigintCached.native width 3

end Airbender.Compiler.MaterializedNative.BigintCached
