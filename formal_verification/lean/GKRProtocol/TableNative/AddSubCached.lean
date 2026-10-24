import GKRProtocol.TableImport
import GKRProtocol.LookupSourceNative.AddSubCached

namespace Airbender.Compiler.TableNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_table_layout native from "artifacts/compiler/add-sub-cached.json"
  source "artifacts/compiler/add-sub-cached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.AddSubCached.native
  native_model Airbender.Compiler.LookupNative.AddSubCached.native
  roles Airbender.Compiler.ConsumerNative.AddSubCached.native.typing

end Airbender.Compiler.TableNative.AddSubCached
