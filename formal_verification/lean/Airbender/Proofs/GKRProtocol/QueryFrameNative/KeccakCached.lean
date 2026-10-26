import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.KeccakCached
import Airbender.Proofs.GKRProtocol.QueryFrameNative.KeccakCachedInputs
import Airbender.Proofs.GKRProtocol.QueryFrameNative.KeccakCachedPart0
import Airbender.Proofs.GKRProtocol.QueryFrameNative.KeccakCachedPart1
import Airbender.Proofs.GKRProtocol.QueryFrameNative.KeccakCachedPart2
import Airbender.Proofs.GKRProtocol.QueryFrameNative.KeccakCachedPart3
import Airbender.Proofs.GKRProtocol.QueryFrameNative.KeccakCachedPart4
import Airbender.Proofs.GKRProtocol.QueryFrameNative.KeccakCachedPart5

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
  counter_model Airbender.Compiler.CounterFrameNative.KeccakCached.native inputs 267 phase 2 start 0 stop 328

end Airbender.Compiler.QueryFrameNative.KeccakCached
