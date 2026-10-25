import GKRProtocol.QueryFrameImport
import GKRProtocol.CounterFrameNative.JumpBranchCached

namespace Airbender.Compiler.QueryFrameNative.JumpBranchCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/jump-branch-cached.json"
  queries (Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.JumpBranchCached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native
  lookup_model Airbender.Compiler.LookupNative.JumpBranchCached.native
  query_model Airbender.Compiler.LookupSourceNative.JumpBranchCached.native
  source_model Airbender.Compiler.SourceContractNative.JumpBranchCached.native
  history_model Airbender.Compiler.HistoryErasureNative.JumpBranchCached.native
  helper_model Airbender.Compiler.HelperValidityNative.JumpBranchCached.native
  counter_model Airbender.Compiler.CounterFrameNative.JumpBranchCached.native inputs 55 phase 3 start 0 stop 55

end Airbender.Compiler.QueryFrameNative.JumpBranchCached
