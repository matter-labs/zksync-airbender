import GKRProtocol.CleanGenericArgumentsImport
import GKRProtocol.CleanArithmeticNative.JumpBranchUncached
import GKRProtocol.FunctionalLinksNative.JumpBranchUncached

namespace Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part0 from "artifacts/compiler/jump-branch-uncached.json"
  certificate "artifacts/compiler/lookup/jump-branch-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native
  lookup_model Airbender.Compiler.LookupNative.JumpBranchUncached.native
  query_model Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.JumpBranchUncached.native
  start 0 stop 4

end Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached.native
