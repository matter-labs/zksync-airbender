import GKRProtocol.QueryFrameImport
import GKRProtocol.CounterFrameNative.BigintCached

namespace Airbender.Compiler.QueryFrameNative.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/bigint-cached.json"
  queries (Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.BigintCached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.BigintCached.native
  lookup_model Airbender.Compiler.LookupNative.BigintCached.native
  query_model Airbender.Compiler.LookupSourceNative.BigintCached.native
  source_model Airbender.Compiler.SourceContractNative.BigintCached.native
  history_model Airbender.Compiler.HistoryErasureNative.BigintCached.native
  helper_model Airbender.Compiler.HelperValidityNative.BigintCached.native
  counter_model Airbender.Compiler.CounterFrameNative.BigintCached.native inputs 277 phase 3 start 0 stop 215

end Airbender.Compiler.QueryFrameNative.BigintCached
