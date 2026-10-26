import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.SubwordMemoryCached

namespace Airbender.Compiler.QueryFrameNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/subword-memory-cached.json"
  queries (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native
  lookup_model Airbender.Compiler.LookupNative.SubwordMemoryCached.native
  query_model Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native
  source_model Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native
  history_model Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached.native
  helper_model Airbender.Compiler.HelperValidityNative.SubwordMemoryCached.native
  counter_model Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native inputs 68 phase 3 start 0 stop 33

end Airbender.Compiler.QueryFrameNative.SubwordMemoryCached
