import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.BlakeGUncached
import Airbender.Proofs.GKRProtocol.TableNative.BlakeGUncached

namespace Airbender.Compiler.CounterFrameNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/blake-g-uncached.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native
  table_model Airbender.Compiler.TableNative.BlakeGUncached.native
  helper_model Airbender.Compiler.HelperNative.BlakeGUncached.native inputs 112 phase 0

end Airbender.Compiler.CounterFrameNative.BlakeGUncached
