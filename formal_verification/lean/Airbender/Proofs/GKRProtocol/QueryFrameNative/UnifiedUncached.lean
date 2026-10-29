import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.UnifiedUncached

namespace Airbender.Compiler.QueryFrameNative.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/unified-uncached.json"
  queries (Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedUncached.native
  lookup_model Airbender.Compiler.LookupNative.UnifiedUncached.native
  query_model Airbender.Compiler.LookupSourceNative.UnifiedUncached.native
  source_model Airbender.Compiler.SourceContractNative.UnifiedUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.UnifiedUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.UnifiedUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.UnifiedUncached.native inputs 137 phase 3 start 0 stop 74

end Airbender.Compiler.QueryFrameNative.UnifiedUncached
