import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.LookupSourceNative.BlakeGCached

namespace Airbender.Compiler.TableNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_table_layout native from "artifacts/compiler/blake-g-cached.json"
  source "artifacts/compiler/blake-g-cached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.BlakeGCached.native
  native_model Airbender.Compiler.LookupNative.BlakeGCached.native
  roles Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing

end Airbender.Compiler.TableNative.BlakeGCached
