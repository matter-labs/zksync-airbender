import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.KeccakUncached
import Airbender.Proofs.GKRProtocol.QueryFrameNative.KeccakUncachedInputs
import Airbender.Proofs.GKRProtocol.QueryFrameNative.KeccakUncachedPart0
import Airbender.Proofs.GKRProtocol.QueryFrameNative.KeccakUncachedPart1
import Airbender.Proofs.GKRProtocol.QueryFrameNative.KeccakUncachedPart2
import Airbender.Proofs.GKRProtocol.QueryFrameNative.KeccakUncachedPart3
import Airbender.Proofs.GKRProtocol.QueryFrameNative.KeccakUncachedPart4
import Airbender.Proofs.GKRProtocol.QueryFrameNative.KeccakUncachedPart5

namespace Airbender.Compiler.QueryFrameNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/keccak-uncached.json"
  queries (Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries)
  base_model Airbender.Compiler.FullArithmeticNative.KeccakUncached.native
  lookup_model Airbender.Compiler.LookupNative.KeccakUncached.native
  query_model Airbender.Compiler.LookupSourceNative.KeccakUncached.native
  source_model Airbender.Compiler.SourceContractNative.KeccakUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.KeccakUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.KeccakUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.KeccakUncached.native inputs 267 phase 2 start 0 stop 328

end Airbender.Compiler.QueryFrameNative.KeccakUncached
