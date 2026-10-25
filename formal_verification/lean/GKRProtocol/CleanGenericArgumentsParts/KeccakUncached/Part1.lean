import GKRProtocol.CleanGenericArgumentsImport
import GKRProtocol.CleanArithmeticNative.KeccakUncached
import GKRProtocol.FunctionalLinksNative.KeccakUncached

namespace Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part1 from "artifacts/compiler/keccak-uncached.json"
  certificate "artifacts/compiler/lookup/keccak-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.KeccakUncached.native
  lookup_model Airbender.Compiler.LookupNative.KeccakUncached.native
  query_model Airbender.Compiler.LookupSourceNative.KeccakUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.KeccakUncached.native
  start 8 stop 16

end Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native
