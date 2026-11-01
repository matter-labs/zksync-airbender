import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.BlakeGCached.Certificate

namespace Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/blake-g-cached.json"
  certificate "artifacts/compiler/lookup/blake-g-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGCached.native
  lookup_model Airbender.Compiler.LookupNative.BlakeGCached.native
  query_model Airbender.Compiler.LookupSourceNative.BlakeGCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.BlakeGCached.native
  start 0 stop 19 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.BlakeGCached

end Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached
