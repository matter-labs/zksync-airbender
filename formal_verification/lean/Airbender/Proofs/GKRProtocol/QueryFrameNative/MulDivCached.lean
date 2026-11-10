import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.MulDivCached
import Airbender.Proofs.GKRProtocol.QueryFrameChecks.MulDivCached.Certificate

namespace Airbender.Compiler.QueryFrameNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_query_frame native certificate "artifacts/compiler/lookup/mul-div-cached.json"
  queries (Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.MulDivCached.native
  lookup_model Airbender.Compiler.LookupNative.MulDivCached.native
  query_model Airbender.Compiler.LookupSourceNative.MulDivCached.native
  source_model Airbender.Compiler.SourceContractNative.MulDivCached.native
  history_model Airbender.Compiler.HistoryErasureNative.MulDivCached.native
  helper_model Airbender.Compiler.HelperValidityNative.MulDivCached.native
  counter_model Airbender.Compiler.CounterFrameNative.MulDivCached.native inputs 71 phase 3 start 0 stop 90
  using_check Airbender.Compiler.QueryFrameChecks.MulDivCached.originalChecked

end Airbender.Compiler.QueryFrameNative.MulDivCached
