import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.JumpBranchUncached.Certificate

namespace Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/jump-branch-uncached.json"
  certificate "artifacts/compiler/lookup/jump-branch-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.JumpBranchUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native
  lookup_model Airbender.Compiler.LookupNative.JumpBranchUncached.native
  query_model Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.JumpBranchUncached.native
  start 0 stop 4 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.JumpBranchUncached

end Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchUncached
