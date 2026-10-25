import GKRProtocol.CleanGenericArgumentsImport
import GKRProtocol.CleanArithmeticNative.MulDivCached
import GKRProtocol.FunctionalLinksNative.MulDivCached

namespace Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part0 from "artifacts/compiler/mul-div-cached.json"
  certificate "artifacts/compiler/lookup/mul-div-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.MulDivCached.native
  base_model Airbender.Compiler.FullArithmeticNative.MulDivCached.native
  lookup_model Airbender.Compiler.LookupNative.MulDivCached.native
  query_model Airbender.Compiler.LookupSourceNative.MulDivCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.MulDivCached.native
  start 0 stop 8

end Airbender.Compiler.CleanGenericArgumentsNative.MulDivCached.native
