import GKRProtocol.TableImport
import GKRProtocol.LookupSourceNative.ShiftBinopCached

namespace Airbender.Compiler.TableNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_table_layout native from "artifacts/compiler/shift-binop-cached.json"
  source "artifacts/compiler/shift-binop-cached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native
  native_model Airbender.Compiler.LookupNative.ShiftBinopCached.native
  roles Airbender.Compiler.ConsumerNative.ShiftBinopCached.native.typing

end Airbender.Compiler.TableNative.ShiftBinopCached
