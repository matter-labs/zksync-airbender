import Airbender.Import.GKRProtocol.CleanGenericArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.WordMemoryUncached

namespace Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part0 from "artifacts/compiler/word-memory-uncached.json"
  certificate "artifacts/compiler/lookup/word-memory-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native
  lookup_model Airbender.Compiler.LookupNative.WordMemoryUncached.native
  query_model Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.WordMemoryUncached.native
  start 0 stop 1

end Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native
