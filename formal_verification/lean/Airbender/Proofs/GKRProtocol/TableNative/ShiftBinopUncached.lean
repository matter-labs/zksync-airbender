import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.LookupSourceNative.ShiftBinopUncached

namespace Airbender.Compiler.TableNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_table_layout native from "artifacts/compiler/shift-binop-uncached.json"
  source "artifacts/compiler/shift-binop-uncached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native
  native_model Airbender.Compiler.LookupNative.ShiftBinopUncached.native
  roles Airbender.Compiler.ConsumerNative.ShiftBinopUncached.native.typing

end Airbender.Compiler.TableNative.ShiftBinopUncached
