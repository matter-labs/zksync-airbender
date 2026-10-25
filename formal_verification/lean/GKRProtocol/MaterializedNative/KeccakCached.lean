import GKRProtocol.MaterializedImport
import GKRProtocol.TableNative.KeccakCached
import Airbender.Data.GKRSetup.Keccak

namespace Airbender.Compiler.MaterializedNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

import_materialized_setup native from "artifacts/compiler/keccak-cached.json"
  uncached "artifacts/compiler/keccak-uncached.json"
  setup_model Airbender.Data.GKRSetup.Keccak
  table_model Airbender.Compiler.TableNative.KeccakCached.native width 8

end Airbender.Compiler.MaterializedNative.KeccakCached
