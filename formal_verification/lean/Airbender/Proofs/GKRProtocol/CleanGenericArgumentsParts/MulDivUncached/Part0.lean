import Airbender.Import.GKRProtocol.CleanGenericArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.MulDivUncached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.MulDivUncached

namespace Airbender.Compiler.CleanGenericArgumentsNative.MulDivUncached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part0 from "artifacts/compiler/mul-div-uncached.json"
  certificate "artifacts/compiler/lookup/mul-div-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.MulDivUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.MulDivUncached.native
  lookup_model Airbender.Compiler.LookupNative.MulDivUncached.native
  query_model Airbender.Compiler.LookupSourceNative.MulDivUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.MulDivUncached.native
  start 0 stop 8

end Airbender.Compiler.CleanGenericArgumentsNative.MulDivUncached.native
