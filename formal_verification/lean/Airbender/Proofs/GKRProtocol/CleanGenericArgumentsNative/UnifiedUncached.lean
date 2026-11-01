import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.UnifiedUncached.Certificate

namespace Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/unified-uncached.json"
  certificate "artifacts/compiler/lookup/unified-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native
  lookup_model Airbender.Compiler.LookupNative.UnifiedUncached.native
  query_model Airbender.Compiler.LookupSourceNative.UnifiedUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.UnifiedUncached.native
  start 0 stop 5 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.UnifiedUncached

end Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached
