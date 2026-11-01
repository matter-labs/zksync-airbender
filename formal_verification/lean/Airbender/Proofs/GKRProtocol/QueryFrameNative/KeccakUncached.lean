import Airbender.Import.GKRProtocol.QueryFrameImport
import Airbender.Proofs.GKRProtocol.CounterFrameNative.KeccakUncached
import Airbender.Proofs.GKRProtocol.QueryFrameChecks.KeccakUncached.Certificate

namespace Airbender.Compiler.QueryFrameNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_query_frame native certificate "artifacts/compiler/lookup/keccak-uncached.json"
  queries (Airbender.Compiler.LookupSourceNative.KeccakUncached.native.genericQueries)
  base_model Airbender.Compiler.FullArithmeticNative.KeccakUncached.native
  lookup_model Airbender.Compiler.LookupNative.KeccakUncached.native
  query_model Airbender.Compiler.LookupSourceNative.KeccakUncached.native
  source_model Airbender.Compiler.SourceContractNative.KeccakUncached.native
  history_model Airbender.Compiler.HistoryErasureNative.KeccakUncached.native
  helper_model Airbender.Compiler.HelperValidityNative.KeccakUncached.native
  counter_model Airbender.Compiler.CounterFrameNative.KeccakUncached.native inputs 266 phase 3 start 0 stop 328
  using_check Airbender.Compiler.QueryFrameChecks.KeccakUncached.originalChecked

end Airbender.Compiler.QueryFrameNative.KeccakUncached
