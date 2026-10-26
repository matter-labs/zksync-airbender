import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.LookupSourceNative.SubwordMemoryUncached

namespace Airbender.Compiler.TableNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_table_layout native from "artifacts/compiler/subword-memory-uncached.json"
  source "artifacts/compiler/subword-memory-uncached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native
  native_model Airbender.Compiler.LookupNative.SubwordMemoryUncached.native
  roles Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing

end Airbender.Compiler.TableNative.SubwordMemoryUncached
