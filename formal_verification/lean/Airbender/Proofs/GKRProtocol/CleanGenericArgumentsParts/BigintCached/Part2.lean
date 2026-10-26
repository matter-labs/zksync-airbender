import Airbender.Import.GKRProtocol.CleanGenericArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.BigintCached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.BigintCached

namespace Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part2 from "artifacts/compiler/bigint-cached.json"
  certificate "artifacts/compiler/lookup/bigint-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.BigintCached.native
  base_model Airbender.Compiler.FullArithmeticNative.BigintCached.native
  lookup_model Airbender.Compiler.LookupNative.BigintCached.native
  query_model Airbender.Compiler.LookupSourceNative.BigintCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.BigintCached.native
  start 16 stop 24

end Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native
