import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.KeccakUncached.Certificate

namespace Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/keccak-uncached.json"
  certificate "artifacts/compiler/lookup/keccak-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.KeccakUncached.native
  lookup_model Airbender.Compiler.LookupNative.KeccakUncached.native
  query_model Airbender.Compiler.LookupSourceNative.KeccakUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.KeccakUncached.native
  start 0 stop 41 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.KeccakUncached

end Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached
