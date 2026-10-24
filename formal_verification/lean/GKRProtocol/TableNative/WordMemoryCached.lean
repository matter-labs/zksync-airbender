import GKRProtocol.TableImport
import GKRProtocol.LookupSourceNative.WordMemoryCached

namespace Airbender.Compiler.TableNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_table_layout native from "artifacts/compiler/word-memory-cached.json"
  source "artifacts/compiler/word-memory-cached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.WordMemoryCached.native
  native_model Airbender.Compiler.LookupNative.WordMemoryCached.native
  roles Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing

end Airbender.Compiler.TableNative.WordMemoryCached
