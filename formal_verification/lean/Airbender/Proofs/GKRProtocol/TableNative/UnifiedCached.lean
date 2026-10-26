import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.LookupSourceNative.UnifiedCached

namespace Airbender.Compiler.TableNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_table_layout native from "artifacts/compiler/unified-cached.json"
  source "artifacts/compiler/unified-cached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.UnifiedCached.native
  native_model Airbender.Compiler.LookupNative.UnifiedCached.native
  roles Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing

end Airbender.Compiler.TableNative.UnifiedCached
