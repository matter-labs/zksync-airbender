import GKRProtocol.QueryFrameImport
import GKRProtocol.CounterFrameNative.BlakeRoundUncached
import GKRProtocol.QueryFrameNative.BlakeRoundUncachedInputs

namespace Airbender.Compiler.QueryFrameNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/blake-round-uncached.json"
  queries (Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native.genericQueries)
  base_model Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native
  lookup_model Airbender.Compiler.LookupNative.BlakeRoundUncached.native
  query_model Airbender.Compiler.LookupSourceNative.BlakeRoundUncached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeRoundUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.BlakeRoundUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.BlakeRoundUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.BlakeRoundUncached.native inputs 763 phase 1 start 448 stop 512

end Airbender.Compiler.QueryFrameNative.BlakeRoundUncached
