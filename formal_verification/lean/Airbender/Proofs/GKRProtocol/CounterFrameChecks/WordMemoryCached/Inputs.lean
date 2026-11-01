import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.WordMemoryCached
import Airbender.Proofs.GKRProtocol.TableNative.WordMemoryCached

namespace Airbender.Compiler.CounterFrameNative.WordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/word-memory-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native
  table_model Airbender.Compiler.TableNative.WordMemoryCached.native
  helper_model Airbender.Compiler.HelperNative.WordMemoryCached.native inputs 52 phase 0

end Airbender.Compiler.CounterFrameNative.WordMemoryCached
