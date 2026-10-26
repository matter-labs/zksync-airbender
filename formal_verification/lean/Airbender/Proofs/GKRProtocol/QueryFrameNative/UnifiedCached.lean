import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.UnifiedCached

namespace Airbender.Compiler.QueryFrameNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/unified-cached.json"
  queries (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedCached.native
  lookup_model Airbender.Compiler.LookupNative.UnifiedCached.native
  query_model Airbender.Compiler.LookupSourceNative.UnifiedCached.native
  source_model Airbender.Compiler.SourceContractNative.UnifiedCached.native
  history_model Airbender.Compiler.HistoryErasureNative.UnifiedCached.native
  helper_model Airbender.Compiler.HelperValidityNative.UnifiedCached.native
  counter_model Airbender.Compiler.CounterFrameNative.UnifiedCached.native inputs 145 phase 3 start 0 stop 74

end Airbender.Compiler.QueryFrameNative.UnifiedCached
