import GKRProtocol.CleanGenericArgumentsImport
import GKRProtocol.CleanArithmeticNative.BlakeRoundCached
import GKRProtocol.FunctionalLinksNative.BlakeRoundCached

namespace Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part9 from "artifacts/compiler/blake-round-cached.json"
  certificate "artifacts/compiler/lookup/blake-round-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native
  lookup_model Airbender.Compiler.LookupNative.BlakeRoundCached.native
  query_model Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.BlakeRoundCached.native
  start 72 stop 80

end Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundCached.native
