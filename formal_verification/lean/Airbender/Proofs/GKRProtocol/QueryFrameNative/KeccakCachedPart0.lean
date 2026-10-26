import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.KeccakCached
import Airbender.Proofs.GKRProtocol.QueryFrameNative.KeccakCachedInputs

namespace Airbender.Compiler.QueryFrameNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/keccak-cached.json"
  queries (Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries)
  base_model Airbender.Compiler.FullArithmeticNative.KeccakCached.native
  lookup_model Airbender.Compiler.LookupNative.KeccakCached.native
  query_model Airbender.Compiler.LookupSourceNative.KeccakCached.native
  source_model Airbender.Compiler.SourceContractNative.KeccakCached.native
  history_model Airbender.Compiler.HistoryErasureNative.KeccakCached.native
  helper_model Airbender.Compiler.HelperValidityNative.KeccakCached.native
  counter_model Airbender.Compiler.CounterFrameNative.KeccakCached.native inputs 266 phase 1 start 0 stop 64

end Airbender.Compiler.QueryFrameNative.KeccakCached
