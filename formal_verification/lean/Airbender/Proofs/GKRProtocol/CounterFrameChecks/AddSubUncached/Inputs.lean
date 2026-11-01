import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.AddSubUncached
import Airbender.Proofs.GKRProtocol.TableNative.AddSubUncached

namespace Airbender.Compiler.CounterFrameNative.AddSubUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/add-sub-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.AddSubUncached.native
  table_model Airbender.Compiler.TableNative.AddSubUncached.native
  helper_model Airbender.Compiler.HelperNative.AddSubUncached.native inputs 48 phase 0

end Airbender.Compiler.CounterFrameNative.AddSubUncached
