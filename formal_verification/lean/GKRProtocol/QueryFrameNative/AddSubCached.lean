import GKRProtocol.QueryFrameImport
import GKRProtocol.CounterFrameNative.AddSubCached

namespace Airbender.Compiler.QueryFrameNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/add-sub-cached.json"
  queries (Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.AddSubCached.native
  lookup_model Airbender.Compiler.LookupNative.AddSubCached.native
  query_model Airbender.Compiler.LookupSourceNative.AddSubCached.native
  source_model Airbender.Compiler.SourceContractNative.AddSubCached.native
  history_model Airbender.Compiler.HistoryErasureNative.AddSubCached.native
  helper_model Airbender.Compiler.HelperValidityNative.AddSubCached.native
  counter_model Airbender.Compiler.CounterFrameNative.AddSubCached.native inputs 48 phase 3 start 0 stop 15

end Airbender.Compiler.QueryFrameNative.AddSubCached
