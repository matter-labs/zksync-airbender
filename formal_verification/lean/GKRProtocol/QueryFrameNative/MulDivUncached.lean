import GKRProtocol.QueryFrameImport
import GKRProtocol.CounterFrameNative.MulDivUncached

namespace Airbender.Compiler.QueryFrameNative.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/mul-div-uncached.json"
  queries (Airbender.Compiler.LookupSourceNative.MulDivUncached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.MulDivUncached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.MulDivUncached.native
  lookup_model Airbender.Compiler.LookupNative.MulDivUncached.native
  query_model Airbender.Compiler.LookupSourceNative.MulDivUncached.native
  source_model Airbender.Compiler.SourceContractNative.MulDivUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.MulDivUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.MulDivUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.MulDivUncached.native inputs 71 phase 3 start 0 stop 90

end Airbender.Compiler.QueryFrameNative.MulDivUncached
