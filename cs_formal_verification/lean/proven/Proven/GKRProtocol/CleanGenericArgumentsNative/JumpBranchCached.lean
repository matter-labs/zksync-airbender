module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.CleanArgumentChecks.JumpBranchCached.Certificate

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/jump-branch-cached.json"
  certificate "artifacts/compiler/lookup/jump-branch-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native
  lookup_model Airbender.Compiler.LookupNative.JumpBranchCached.native
  query_model Airbender.Compiler.LookupSourceNative.JumpBranchCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.JumpBranchCached.native
  start 0 stop 4 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.JumpBranchCached

end Airbender.Compiler.CleanGenericArgumentsNative.JumpBranchCached
