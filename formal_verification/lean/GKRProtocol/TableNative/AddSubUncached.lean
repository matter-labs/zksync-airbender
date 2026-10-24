import GKRProtocol.TableImport
import GKRProtocol.LookupSourceNative.AddSubUncached

namespace Airbender.Compiler.TableNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_table_layout native from "artifacts/compiler/add-sub-uncached.json"
  source "artifacts/compiler/add-sub-uncached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.AddSubUncached.native
  native_model Airbender.Compiler.LookupNative.AddSubUncached.native
  roles Airbender.Compiler.ConsumerNative.AddSubUncached.native.typing

end Airbender.Compiler.TableNative.AddSubUncached
