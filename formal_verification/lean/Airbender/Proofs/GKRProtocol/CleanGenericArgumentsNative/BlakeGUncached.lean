import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.BlakeGUncached.Certificate

namespace Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/blake-g-uncached.json"
  certificate "artifacts/compiler/lookup/blake-g-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native
  lookup_model Airbender.Compiler.LookupNative.BlakeGUncached.native
  query_model Airbender.Compiler.LookupSourceNative.BlakeGUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.BlakeGUncached.native
  start 0 stop 19 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.BlakeGUncached

end Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached
