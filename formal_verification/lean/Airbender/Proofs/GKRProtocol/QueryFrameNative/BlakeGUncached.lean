import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.BlakeGUncached

namespace Airbender.Compiler.QueryFrameNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_query_frame native certificate "artifacts/compiler/lookup/blake-g-uncached.json"
  queries (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.genericQueries)
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native
  lookup_model Airbender.Compiler.LookupNative.BlakeGUncached.native
  query_model Airbender.Compiler.LookupSourceNative.BlakeGUncached.native
  source_model Airbender.Compiler.SourceContractNative.BlakeGUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.BlakeGUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.BlakeGUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.BlakeGUncached.native inputs 112 phase 3 start 0 stop 171

end Airbender.Compiler.QueryFrameNative.BlakeGUncached
