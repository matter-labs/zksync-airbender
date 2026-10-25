import GKRProtocol.MaterializedImport
import GKRProtocol.TableNative.KeccakUncached
import Airbender.Data.GKRSetup.Keccak

namespace Airbender.Compiler.MaterializedNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_materialized_setup native from "artifacts/compiler/keccak-uncached.json"
  uncached "artifacts/compiler/keccak-uncached.json"
  setup_model Airbender.Data.GKRSetup.Keccak
  table_model Airbender.Compiler.TableNative.KeccakUncached.native width 8

end Airbender.Compiler.MaterializedNative.KeccakUncached
