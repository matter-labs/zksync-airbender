import GKRProtocol.TableImport
import GKRProtocol.LookupSourceNative.BigintUncached

namespace Airbender.Compiler.TableNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_table_layout native from "artifacts/compiler/bigint-uncached.json"
  source "artifacts/compiler/bigint-uncached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.BigintUncached.native
  native_model Airbender.Compiler.LookupNative.BigintUncached.native
  roles Airbender.Compiler.ConsumerNative.BigintUncached.native.typing

end Airbender.Compiler.TableNative.BigintUncached
