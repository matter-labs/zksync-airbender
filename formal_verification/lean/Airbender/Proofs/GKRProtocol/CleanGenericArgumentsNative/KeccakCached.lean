import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.KeccakCached.Certificate

namespace Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/keccak-cached.json"
  certificate "artifacts/compiler/lookup/keccak-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.KeccakCached.native
  base_model Airbender.Compiler.FullArithmeticNative.KeccakCached.native
  lookup_model Airbender.Compiler.LookupNative.KeccakCached.native
  query_model Airbender.Compiler.LookupSourceNative.KeccakCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.KeccakCached.native
  start 0 stop 41 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.KeccakCached

end Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached
