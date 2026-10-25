import GKRProtocol.QueryFrameImport
import GKRProtocol.CounterFrameNative.ShiftBinopUncached

namespace Airbender.Compiler.QueryFrameNative.ShiftBinopUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/shift-binop-uncached.json"
  queries (Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native
  lookup_model Airbender.Compiler.LookupNative.ShiftBinopUncached.native
  query_model Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native
  source_model Airbender.Compiler.SourceContractNative.ShiftBinopUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.ShiftBinopUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.ShiftBinopUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.ShiftBinopUncached.native inputs 98 phase 3 start 0 stop 63

end Airbender.Compiler.QueryFrameNative.ShiftBinopUncached
