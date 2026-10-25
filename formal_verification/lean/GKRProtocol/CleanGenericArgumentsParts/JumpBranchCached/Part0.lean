import GKRProtocol.CleanGenericArgumentsImport
import GKRProtocol.CleanArithmeticNative.JumpBranchCached
import GKRProtocol.FunctionalLinksNative.JumpBranchCached

namespace Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part0 from "artifacts/compiler/jump-branch-cached.json"
  certificate "artifacts/compiler/lookup/jump-branch-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native
  lookup_model Airbender.Compiler.LookupNative.JumpBranchCached.native
  query_model Airbender.Compiler.LookupSourceNative.JumpBranchCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native
  start 0 stop 4

end Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached.native
