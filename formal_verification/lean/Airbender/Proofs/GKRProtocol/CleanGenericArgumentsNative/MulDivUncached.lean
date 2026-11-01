import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.MulDivUncached.Certificate

namespace Airbender.Compiler.CleanGenericArgumentsNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/mul-div-uncached.json"
  certificate "artifacts/compiler/lookup/mul-div-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.MulDivUncached.native
  lookup_model Airbender.Compiler.LookupNative.MulDivUncached.native
  query_model Airbender.Compiler.LookupSourceNative.MulDivUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.MulDivUncached.native
  start 0 stop 8 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.MulDivUncached

end Airbender.Compiler.CleanGenericArgumentsNative.MulDivUncached
