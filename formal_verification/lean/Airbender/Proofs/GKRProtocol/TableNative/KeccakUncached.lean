import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.LookupSourceNative.KeccakUncached

namespace Airbender.Compiler.TableNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_table_layout native from "artifacts/compiler/keccak-uncached.json"
  source "artifacts/compiler/keccak-uncached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.KeccakUncached.native
  native_model Airbender.Compiler.LookupNative.KeccakUncached.native
  roles Airbender.Compiler.ConsumerNative.KeccakUncached.native.typing

end Airbender.Compiler.TableNative.KeccakUncached
