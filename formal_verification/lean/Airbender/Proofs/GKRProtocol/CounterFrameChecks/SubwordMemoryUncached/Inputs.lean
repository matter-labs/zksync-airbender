import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.TableNative.SubwordMemoryUncached

namespace Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/subword-memory-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native
  table_model Airbender.Compiler.TableNative.SubwordMemoryUncached.native
  helper_model Airbender.Compiler.HelperNative.SubwordMemoryUncached.native inputs 68 phase 0

end Airbender.Compiler.CounterFrameNative.SubwordMemoryUncached
