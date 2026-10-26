import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.BlakeRoundCached
import Airbender.Proofs.GKRProtocol.QueryFrameNative.BlakeRoundCachedInputs

namespace Airbender.Compiler.QueryFrameNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/blake-round-cached.json"
  queries (Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native.genericQueries)
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native
  lookup_model Airbender.Compiler.LookupNative.BlakeRoundCached.native
  query_model Airbender.Compiler.LookupSourceNative.BlakeRoundCached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeRoundCached.native
  history_model Airbender.Compiler.HistoryErasureNative.BlakeRoundCached.native
  helper_model Airbender.Compiler.HelperValidityNative.BlakeRoundCached.native
  counter_model Airbender.Compiler.CounterFrameNative.BlakeRoundCached.native inputs 763 phase 1 start 1088 stop 1152

end Airbender.Compiler.QueryFrameNative.BlakeRoundCached
