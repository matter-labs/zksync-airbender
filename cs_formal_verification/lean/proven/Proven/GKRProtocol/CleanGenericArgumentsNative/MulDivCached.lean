module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.CleanArgumentChecks.MulDivCached.Certificate

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/mul-div-cached.json"
  certificate "artifacts/compiler/lookup/mul-div-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.MulDivCached.native
  base_model Airbender.Compiler.FullArithmeticNative.MulDivCached.native
  lookup_model Airbender.Compiler.LookupNative.MulDivCached.native
  query_model Airbender.Compiler.LookupSourceNative.MulDivCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.MulDivCached.native
  start 0 stop 8 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.MulDivCached

end Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached
