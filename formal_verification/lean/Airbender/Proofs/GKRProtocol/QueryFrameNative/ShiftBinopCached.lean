import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.QueryFrameChecks.ShiftBinopCached.Certificate

namespace Airbender.Compiler.QueryFrameNative.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_query_frame native certificate "artifacts/compiler/lookup/shift-binop-cached.json"
  queries (Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native
  lookup_model Airbender.Compiler.LookupNative.ShiftBinopCached.native
  query_model Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native
  source_model Airbender.Compiler.SourceContractNative.ShiftBinopCached.native
  history_model Airbender.Compiler.HistoryErasureNative.ShiftBinopCached.native
  helper_model Airbender.Compiler.HelperValidityNative.ShiftBinopCached.native
  counter_model Airbender.Compiler.CounterFrameNative.ShiftBinopCached.native inputs 98 phase 3 start 0 stop 63
  using_check Airbender.Compiler.QueryFrameChecks.ShiftBinopCached.originalChecked

end Airbender.Compiler.QueryFrameNative.ShiftBinopCached
