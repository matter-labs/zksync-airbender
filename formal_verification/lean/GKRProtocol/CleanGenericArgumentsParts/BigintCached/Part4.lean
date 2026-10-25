import GKRProtocol.CleanGenericArgumentsImport
import GKRProtocol.CleanArithmeticNative.BigintCached
import GKRProtocol.FunctionalLinksNative.BigintCached

namespace Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part4 from "artifacts/compiler/bigint-cached.json"
  certificate "artifacts/compiler/lookup/bigint-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.BigintCached.native
  base_model Airbender.Compiler.FullArithmeticNative.BigintCached.native
  lookup_model Airbender.Compiler.LookupNative.BigintCached.native
  query_model Airbender.Compiler.LookupSourceNative.BigintCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.BigintCached.native
  start 32 stop 40

end Airbender.Compiler.CleanGenericArgumentsNative.BigintCached.native
