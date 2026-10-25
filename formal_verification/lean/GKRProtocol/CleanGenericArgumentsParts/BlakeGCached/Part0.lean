import GKRProtocol.CleanGenericArgumentsImport
import GKRProtocol.CleanArithmeticNative.BlakeGCached
import GKRProtocol.FunctionalLinksNative.BlakeGCached

namespace Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part0 from "artifacts/compiler/blake-g-cached.json"
  certificate "artifacts/compiler/lookup/blake-g-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGCached.native
  lookup_model Airbender.Compiler.LookupNative.BlakeGCached.native
  query_model Airbender.Compiler.LookupSourceNative.BlakeGCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.BlakeGCached.native
  start 0 stop 8

end Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native
