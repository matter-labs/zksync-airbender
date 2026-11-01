import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.BigintCached.Certificate

namespace Airbender.Compiler.CleanGenericArgumentsNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/bigint-cached.json"
  certificate "artifacts/compiler/lookup/bigint-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.BigintCached.native
  base_model Airbender.Compiler.FullArithmeticNative.BigintCached.native
  lookup_model Airbender.Compiler.LookupNative.BigintCached.native
  query_model Airbender.Compiler.LookupSourceNative.BigintCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.BigintCached.native
  start 0 stop 61 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.BigintCached

end Airbender.Compiler.CleanGenericArgumentsNative.BigintCached
