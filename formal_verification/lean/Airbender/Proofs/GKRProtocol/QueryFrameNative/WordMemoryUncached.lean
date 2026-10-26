import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.WordMemoryUncached

namespace Airbender.Compiler.QueryFrameNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/word-memory-uncached.json"
  queries (Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native
  lookup_model Airbender.Compiler.LookupNative.WordMemoryUncached.native
  query_model Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native
  source_model Airbender.Compiler.SourceContractNative.WordMemoryUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.WordMemoryUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.WordMemoryUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.WordMemoryUncached.native inputs 52 phase 3 start 0 stop 22

end Airbender.Compiler.QueryFrameNative.WordMemoryUncached
