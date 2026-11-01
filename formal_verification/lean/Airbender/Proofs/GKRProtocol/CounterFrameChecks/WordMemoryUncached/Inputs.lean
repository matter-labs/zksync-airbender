import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.WordMemoryUncached
import Airbender.Proofs.GKRProtocol.TableNative.WordMemoryUncached

namespace Airbender.Compiler.CounterFrameNative.WordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/word-memory-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native
  table_model Airbender.Compiler.TableNative.WordMemoryUncached.native
  helper_model Airbender.Compiler.HelperNative.WordMemoryUncached.native inputs 52 phase 0

end Airbender.Compiler.CounterFrameNative.WordMemoryUncached
