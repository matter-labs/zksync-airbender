import Airbender.Import.GKRProtocol.MaterializedImport
import Airbender.Proofs.GKRProtocol.TableNative.MulDivCached
import Airbender.Data.GKRSetup.MulDiv

namespace Airbender.Compiler.MaterializedNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_materialized_setup native from "artifacts/compiler/mul-div-cached.json"
  uncached "artifacts/compiler/mul-div-uncached.json"
  setup_model Airbender.Data.GKRSetup.MulDiv
  table_model Airbender.Compiler.TableNative.MulDivCached.native width 9

end Airbender.Compiler.MaterializedNative.MulDivCached
