import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.KeccakUncached
import Airbender.Proofs.GKRProtocol.TableNative.KeccakUncached

namespace Airbender.Compiler.CounterFrameNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/keccak-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.KeccakUncached.native
  table_model Airbender.Compiler.TableNative.KeccakUncached.native
  helper_model Airbender.Compiler.HelperNative.KeccakUncached.native inputs 266 phase 0

end Airbender.Compiler.CounterFrameNative.KeccakUncached
