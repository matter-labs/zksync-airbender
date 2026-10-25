import GKRProtocol.QueryFrameImport
import GKRProtocol.CounterFrameNative.JumpBranchUncached

namespace Airbender.Compiler.QueryFrameNative.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/jump-branch-uncached.json"
  queries (Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native
  lookup_model Airbender.Compiler.LookupNative.JumpBranchUncached.native
  query_model Airbender.Compiler.LookupSourceNative.JumpBranchUncached.native
  source_model Airbender.Compiler.SourceContractNative.JumpBranchUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.JumpBranchUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.JumpBranchUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.JumpBranchUncached.native inputs 55 phase 3 start 0 stop 55

end Airbender.Compiler.QueryFrameNative.JumpBranchUncached
