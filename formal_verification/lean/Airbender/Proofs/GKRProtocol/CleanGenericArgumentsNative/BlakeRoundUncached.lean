import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.BlakeRoundUncached.Certificate

namespace Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_clean_generic_arguments native from "artifacts/compiler/blake-round-uncached.json"
  certificate "artifacts/compiler/lookup/blake-round-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native
  lookup_model Airbender.Compiler.LookupNative.BlakeRoundUncached.native
  query_model Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.BlakeRoundUncached.native
  start 0 stop 192 part_size 8 phase 1 using_checks Airbender.Compiler.CleanArgumentChecks.BlakeRoundUncached

end Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached
