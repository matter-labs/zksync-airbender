import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.AddSubCached
import Airbender.Proofs.GKRProtocol.QueryFrameChecks.AddSubCached.Certificate

namespace Airbender.Compiler.QueryFrameNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_query_frame native certificate "artifacts/compiler/lookup/add-sub-cached.json"
  queries (Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.AddSubCached.native
  lookup_model Airbender.Compiler.LookupNative.AddSubCached.native
  query_model Airbender.Compiler.LookupSourceNative.AddSubCached.native
  source_model Airbender.Compiler.SourceContractNative.AddSubCached.native
  history_model Airbender.Compiler.HistoryErasureNative.AddSubCached.native
  helper_model Airbender.Compiler.HelperValidityNative.AddSubCached.native
  counter_model Airbender.Compiler.CounterFrameNative.AddSubCached.native inputs 48 phase 3 start 0 stop 15
  using_check Airbender.Compiler.QueryFrameChecks.AddSubCached.originalChecked

end Airbender.Compiler.QueryFrameNative.AddSubCached
