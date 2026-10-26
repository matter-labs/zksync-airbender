import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.LookupSourceNative.JumpBranchUncached

namespace Airbender.Compiler.TableNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_source_table_layout native from "artifacts/compiler/jump-branch-uncached.json"
  source "artifacts/compiler/jump-branch-uncached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native
  native_model Airbender.Compiler.LookupNative.JumpBranchUncached.native
  roles Airbender.Compiler.ConsumerNative.JumpBranchUncached.native.typing

end Airbender.Compiler.TableNative.JumpBranchUncached
