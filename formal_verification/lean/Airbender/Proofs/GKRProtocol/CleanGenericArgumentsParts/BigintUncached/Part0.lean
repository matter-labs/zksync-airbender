import Airbender.Import.GKRProtocol.CleanGenericArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.BigintUncached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.BigintUncached

namespace Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part0 from "artifacts/compiler/bigint-uncached.json"
  certificate "artifacts/compiler/lookup/bigint-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.BigintUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.BigintUncached.native
  lookup_model Airbender.Compiler.LookupNative.BigintUncached.native
  query_model Airbender.Compiler.LookupSourceNative.BigintUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.BigintUncached.native
  start 0 stop 8

end Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native
