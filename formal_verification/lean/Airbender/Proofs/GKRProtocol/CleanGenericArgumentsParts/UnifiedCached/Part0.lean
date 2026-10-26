import Airbender.Import.GKRProtocol.CleanGenericArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.UnifiedCached

namespace Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part0 from "artifacts/compiler/unified-cached.json"
  certificate "artifacts/compiler/lookup/unified-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedCached.native
  lookup_model Airbender.Compiler.LookupNative.UnifiedCached.native
  query_model Airbender.Compiler.LookupSourceNative.UnifiedCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.UnifiedCached.native
  start 0 stop 5

end Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native
