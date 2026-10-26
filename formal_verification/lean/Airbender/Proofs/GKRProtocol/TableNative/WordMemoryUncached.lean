import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.LookupSourceNative.WordMemoryUncached

namespace Airbender.Compiler.TableNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_table_layout native from "artifacts/compiler/word-memory-uncached.json"
  source "artifacts/compiler/word-memory-uncached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native
  native_model Airbender.Compiler.LookupNative.WordMemoryUncached.native
  roles Airbender.Compiler.ConsumerNative.WordMemoryUncached.native.typing

end Airbender.Compiler.TableNative.WordMemoryUncached
