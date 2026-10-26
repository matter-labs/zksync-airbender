import Airbender.Import.GKRProtocol.CleanGenericArgumentsImport
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.KeccakCached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.KeccakCached

namespace Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_clean_generic_arguments part0 from "artifacts/compiler/keccak-cached.json"
  certificate "artifacts/compiler/lookup/keccak-cached.json"
  clean_model Airbender.Compiler.CleanArithmeticNative.KeccakCached.native
  base_model Airbender.Compiler.FullArithmeticNative.KeccakCached.native
  lookup_model Airbender.Compiler.LookupNative.KeccakCached.native
  query_model Airbender.Compiler.LookupSourceNative.KeccakCached.native
  links_model Airbender.Compiler.FunctionalLinksNative.KeccakCached.native
  start 0 stop 8

end Airbender.Compiler.CleanGenericArgumentsNative.KeccakCached.native
