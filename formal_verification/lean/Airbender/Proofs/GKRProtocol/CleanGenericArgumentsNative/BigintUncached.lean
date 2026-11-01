import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.BigintUncached.Certificate

namespace Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/bigint-uncached.json"
  certificate "artifacts/compiler/lookup/bigint-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.BigintUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.BigintUncached.native
  lookup_model Airbender.Compiler.LookupNative.BigintUncached.native
  query_model Airbender.Compiler.LookupSourceNative.BigintUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.BigintUncached.native
  start 0 stop 61 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.BigintUncached

end Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached
