import GKRProtocol.CleanGenericArgumentsImport
import GKRProtocol.CleanArithmeticNative.SubwordMemoryUncached
import GKRProtocol.FunctionalLinksNative.SubwordMemoryUncached

namespace Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part0 from "artifacts/compiler/subword-memory-uncached.json"
  certificate "artifacts/compiler/lookup/subword-memory-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native
  lookup_model Airbender.Compiler.LookupNative.SubwordMemoryUncached.native
  query_model Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native
  start 0 stop 2

end Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryUncached.native
