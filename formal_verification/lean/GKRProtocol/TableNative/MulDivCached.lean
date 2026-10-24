import GKRProtocol.TableImport
import GKRProtocol.LookupSourceNative.MulDivCached

namespace Airbender.Compiler.TableNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_table_layout native from "artifacts/compiler/mul-div-cached.json"
  source "artifacts/compiler/mul-div-cached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.MulDivCached.native
  native_model Airbender.Compiler.LookupNative.MulDivCached.native
  roles Airbender.Compiler.ConsumerNative.MulDivCached.native.typing

end Airbender.Compiler.TableNative.MulDivCached
