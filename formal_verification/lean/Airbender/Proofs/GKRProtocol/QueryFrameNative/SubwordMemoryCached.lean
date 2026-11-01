import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.QueryFrameChecks.SubwordMemoryCached.Certificate

namespace Airbender.Compiler.QueryFrameNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_query_frame native certificate "artifacts/compiler/lookup/subword-memory-cached.json"
  queries (Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.genericQueries ++ Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native.range16Queries)
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native
  lookup_model Airbender.Compiler.LookupNative.SubwordMemoryCached.native
  query_model Airbender.Compiler.LookupSourceNative.SubwordMemoryCached.native
  source_model Airbender.Compiler.SourceContractNative.SubwordMemoryCached.native
  history_model Airbender.Compiler.HistoryErasureNative.SubwordMemoryCached.native
  helper_model Airbender.Compiler.HelperValidityNative.SubwordMemoryCached.native
  counter_model Airbender.Compiler.CounterFrameNative.SubwordMemoryCached.native inputs 68 phase 3 start 0 stop 33
  using_check Airbender.Compiler.QueryFrameChecks.SubwordMemoryCached.originalChecked

end Airbender.Compiler.QueryFrameNative.SubwordMemoryCached
