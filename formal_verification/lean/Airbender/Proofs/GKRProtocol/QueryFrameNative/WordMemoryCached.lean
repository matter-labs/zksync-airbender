import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.WordMemoryCached

namespace Airbender.Compiler.QueryFrameNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/word-memory-cached.json"
  queries (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native
  lookup_model Airbender.Compiler.LookupNative.WordMemoryCached.native
  query_model Airbender.Compiler.LookupSourceNative.WordMemoryCached.native
  source_model Airbender.Compiler.SourceContractNative.WordMemoryCached.native
  history_model Airbender.Compiler.HistoryErasureNative.WordMemoryCached.native
  helper_model Airbender.Compiler.HelperValidityNative.WordMemoryCached.native
  counter_model Airbender.Compiler.CounterFrameNative.WordMemoryCached.native inputs 52 phase 3 start 0 stop 22

end Airbender.Compiler.QueryFrameNative.WordMemoryCached
