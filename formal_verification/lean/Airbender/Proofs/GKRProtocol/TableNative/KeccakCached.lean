import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.LookupSourceNative.KeccakCached

namespace Airbender.Compiler.TableNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_table_layout native from "artifacts/compiler/keccak-cached.json"
  source "artifacts/compiler/keccak-cached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.KeccakCached.native
  native_model Airbender.Compiler.LookupNative.KeccakCached.native
  roles Airbender.Compiler.ConsumerNative.KeccakCached.native.typing

end Airbender.Compiler.TableNative.KeccakCached
