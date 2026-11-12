module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.CleanArgumentChecks.UnifiedCached.Certificate

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/unified-cached.json"
  certificate "artifacts/compiler/lookup/unified-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedCached.native
  lookup_model Airbender.Compiler.LookupNative.UnifiedCached.native
  query_model Airbender.Compiler.LookupSourceNative.UnifiedCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native
  start 0 stop 5 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.UnifiedCached

end Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached
