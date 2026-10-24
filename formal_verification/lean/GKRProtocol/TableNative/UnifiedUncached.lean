import GKRProtocol.TableImport
import GKRProtocol.LookupSourceNative.UnifiedUncached

namespace Airbender.Compiler.TableNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_table_layout native from "artifacts/compiler/unified-uncached.json"
  source "artifacts/compiler/unified-uncached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.UnifiedUncached.native
  native_model Airbender.Compiler.LookupNative.UnifiedUncached.native
  roles Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing

end Airbender.Compiler.TableNative.UnifiedUncached
