import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.SubwordMemoryCached
import Airbender.Proofs.GKRProtocol.TableNative.SubwordMemoryCached

namespace Airbender.Compiler.CounterFrameNative.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/subword-memory-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native
  table_model Airbender.Compiler.TableNative.SubwordMemoryCached.native
  helper_model Airbender.Compiler.HelperNative.SubwordMemoryCached.native inputs 68 phase 0

end Airbender.Compiler.CounterFrameNative.SubwordMemoryCached
