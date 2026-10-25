import GKRProtocol.CleanGenericArgumentsImport
import GKRProtocol.CleanArithmeticNative.BlakeGUncached
import GKRProtocol.FunctionalLinksNative.BlakeGUncached

namespace Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part1 from "artifacts/compiler/blake-g-uncached.json"
  certificate "artifacts/compiler/lookup/blake-g-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native
  lookup_model Airbender.Compiler.LookupNative.BlakeGUncached.native
  query_model Airbender.Compiler.LookupSourceNative.BlakeGUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.BlakeGUncached.native
  start 8 stop 16

end Airbender.Compiler.CleanGenericArgumentsNative.BlakeGUncached.native
