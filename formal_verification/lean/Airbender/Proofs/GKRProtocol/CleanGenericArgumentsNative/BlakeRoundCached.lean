import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.BlakeRoundCached.Certificate

namespace Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/blake-round-cached.json"
  certificate "artifacts/compiler/lookup/blake-round-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native
  lookup_model Airbender.Compiler.LookupNative.BlakeRoundCached.native
  query_model Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.BlakeRoundCached.native
  start 0 stop 192 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.BlakeRoundCached

end Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached
