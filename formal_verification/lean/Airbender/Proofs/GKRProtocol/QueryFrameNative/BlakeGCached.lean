import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.BlakeGCached

namespace Airbender.Compiler.QueryFrameNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/blake-g-cached.json"
  queries (Airbender.Compiler.LookupSourceNative.BlakeGCached.native.genericQueries)
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGCached.native
  lookup_model Airbender.Compiler.LookupNative.BlakeGCached.native
  query_model Airbender.Compiler.LookupSourceNative.BlakeGCached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeGCached.native
  history_model Airbender.Compiler.HistoryErasureNative.BlakeGCached.native
  helper_model Airbender.Compiler.HelperValidityNative.BlakeGCached.native
  counter_model Airbender.Compiler.CounterFrameNative.BlakeGCached.native inputs 113 phase 3 start 0 stop 171

end Airbender.Compiler.QueryFrameNative.BlakeGCached
