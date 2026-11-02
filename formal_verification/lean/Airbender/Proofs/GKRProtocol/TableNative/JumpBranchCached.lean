import Airbender.Import.GKRProtocol.TableImport
import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.JumpBranchCached.Certificate

namespace Airbender.Compiler.TableNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_source_table_layout native from "artifacts/compiler/jump-branch-cached.json"
  source "artifacts/compiler/jump-branch-cached-source.json"
  source_lookups Airbender.Compiler.LookupSourceNative.JumpBranchCached.native
  native_model Airbender.Compiler.LookupNative.JumpBranchCached.native
  roles Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing
  using_freshness Airbender.Compiler.SourceFreshnessChecks.JumpBranchCached

end Airbender.Compiler.TableNative.JumpBranchCached
