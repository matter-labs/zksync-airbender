import Airbender.Import.GKRProtocol.CleanGenericArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.WordMemoryCached

namespace Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part0 from "artifacts/compiler/word-memory-cached.json"
  certificate "artifacts/compiler/lookup/word-memory-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native
  lookup_model Airbender.Compiler.LookupNative.WordMemoryCached.native
  query_model Airbender.Compiler.LookupSourceNative.WordMemoryCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.WordMemoryCached.native
  start 0 stop 1

end Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native
