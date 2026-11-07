import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.KeccakCached
import Airbender.Proofs.GKRProtocol.TableNative.KeccakCached

namespace Airbender.Compiler.CounterFrameNative.KeccakCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/keccak-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.KeccakCached.native
  table_model Airbender.Compiler.TableNative.KeccakCached.native
  helper_model Airbender.Compiler.HelperNative.KeccakCached.native inputs 266 phase 0

end Airbender.Compiler.CounterFrameNative.KeccakCached
