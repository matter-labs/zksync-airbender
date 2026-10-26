import Airbender.Import.GKRProtocol.CleanGenericArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.BlakeRoundUncached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.BlakeRoundUncached

namespace Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part19 from "artifacts/compiler/blake-round-uncached.json"
  certificate "artifacts/compiler/lookup/blake-round-uncached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native
  lookup_model Airbender.Compiler.LookupNative.BlakeRoundUncached.native
  query_model Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native
  links_model Airbender.Compiler.FunctionalLinksNative.BlakeRoundUncached.native
  start 152 stop 160

end Airbender.Compiler.CleanGenericArgumentsNative.BlakeRoundUncached.native
