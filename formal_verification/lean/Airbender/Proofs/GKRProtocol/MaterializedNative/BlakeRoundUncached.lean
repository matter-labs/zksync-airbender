import Airbender.Import.GKRProtocol.MaterializedImport
import Airbender.Proofs.GKRProtocol.TableNative.BlakeRoundUncached
import Airbender.Data.GKRSetup.BlakeRound

namespace Airbender.Compiler.MaterializedNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_materialized_setup native from "artifacts/compiler/blake-round-uncached.json"
  uncached "artifacts/compiler/blake-round-uncached.json"
  setup_model Airbender.Data.GKRSetup.BlakeRound
  table_model Airbender.Compiler.TableNative.BlakeRoundUncached.native width 6

end Airbender.Compiler.MaterializedNative.BlakeRoundUncached
