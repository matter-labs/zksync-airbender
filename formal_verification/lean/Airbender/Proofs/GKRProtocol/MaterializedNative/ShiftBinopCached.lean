import Airbender.Import.GKRProtocol.MaterializedImport
import Airbender.Proofs.GKRProtocol.TableNative.ShiftBinopCached
import Airbender.Data.GKRSetup.ShiftBinop

namespace Airbender.Compiler.MaterializedNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_materialized_setup native from "artifacts/compiler/shift-binop-cached.json"
  uncached "artifacts/compiler/shift-binop-uncached.json"
  setup_model Airbender.Data.GKRSetup.ShiftBinop
  table_model Airbender.Compiler.TableNative.ShiftBinopCached.native width 10

end Airbender.Compiler.MaterializedNative.ShiftBinopCached
