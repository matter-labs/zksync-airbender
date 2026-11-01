import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.SubwordMemoryCached.Certificate

namespace Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/subword-memory-cached.json"
  certificate "artifacts/compiler/lookup/subword-memory-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native
  lookup_model Airbender.Compiler.LookupNative.SubwordMemoryCached.native
  query_model Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.SubwordMemoryCached.native
  start 0 stop 2 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.SubwordMemoryCached

end Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached
