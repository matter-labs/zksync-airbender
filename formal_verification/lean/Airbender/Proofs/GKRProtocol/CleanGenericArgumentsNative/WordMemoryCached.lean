import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.WordMemoryCached.Certificate

namespace Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/word-memory-cached.json"
  certificate "artifacts/compiler/lookup/word-memory-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native
  lookup_model Airbender.Compiler.LookupNative.WordMemoryCached.native
  query_model Airbender.Compiler.LookupSourceNative.WordMemoryCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.WordMemoryCached.native
  start 0 stop 1 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.WordMemoryCached

end Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached
