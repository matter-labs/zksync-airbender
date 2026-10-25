import GKRProtocol.QueryFrameImport
import GKRProtocol.CounterFrameNative.SubwordMemoryUncached

namespace Airbender.Compiler.QueryFrameNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/subword-memory-uncached.json"
  queries (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native
  lookup_model Airbender.Compiler.LookupNative.SubwordMemoryUncached.native
  query_model Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native
  source_model Airbender.Compiler.SourceContractNative.SubwordMemoryUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.SubwordMemoryUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.SubwordMemoryUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached.native inputs 68 phase 3 start 0 stop 33

end Airbender.Compiler.QueryFrameNative.SubwordMemoryUncached
