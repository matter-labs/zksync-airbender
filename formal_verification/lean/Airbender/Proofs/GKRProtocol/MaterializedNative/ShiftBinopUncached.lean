import Airbender.Import.GKRProtocol.MaterializedImport
import Airbender.Proofs.GKRProtocol.TableNative.ShiftBinopUncached
import Airbender.Data.GKRSetup.ShiftBinop

namespace Airbender.Compiler.MaterializedNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_materialized_setup native from "artifacts/compiler/shift-binop-uncached.json"
  uncached "artifacts/compiler/shift-binop-uncached.json"
  setup_model Airbender.Data.GKRSetup.ShiftBinop
  table_model Airbender.Compiler.TableNative.ShiftBinopUncached.native width 10

end Airbender.Compiler.MaterializedNative.ShiftBinopUncached
