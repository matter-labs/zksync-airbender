import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.AddSubUncached

namespace Airbender.Compiler.QueryFrameNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/add-sub-uncached.json"
  queries (Airbender.Compiler.LookupSourceNative.AddSubUncached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.AddSubUncached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.AddSubUncached.native
  lookup_model Airbender.Compiler.LookupNative.AddSubUncached.native
  query_model Airbender.Compiler.LookupSourceNative.AddSubUncached.native
  source_model Airbender.Compiler.SourceContractNative.AddSubUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.AddSubUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.AddSubUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.AddSubUncached.native inputs 48 phase 3 start 0 stop 15

end Airbender.Compiler.QueryFrameNative.AddSubUncached
