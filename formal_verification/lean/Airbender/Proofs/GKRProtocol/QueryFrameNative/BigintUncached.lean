import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.BigintUncached

namespace Airbender.Compiler.QueryFrameNative.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/bigint-uncached.json"
  queries (Airbender.Compiler.LookupSourceNative.BigintUncached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.BigintUncached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.BigintUncached.native
  lookup_model Airbender.Compiler.LookupNative.BigintUncached.native
  query_model Airbender.Compiler.LookupSourceNative.BigintUncached.native
  source_model Airbender.Compiler.SourceContractNative.BigintUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.BigintUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.BigintUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.BigintUncached.native inputs 277 phase 3 start 0 stop 215

end Airbender.Compiler.QueryFrameNative.BigintUncached
