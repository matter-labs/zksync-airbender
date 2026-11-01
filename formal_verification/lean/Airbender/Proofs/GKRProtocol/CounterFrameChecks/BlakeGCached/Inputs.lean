import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.BlakeGCached
import Airbender.Proofs.GKRProtocol.TableNative.BlakeGCached

namespace Airbender.Compiler.CounterFrameNative.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/blake-g-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.BlakeGCached.native
  table_model Airbender.Compiler.TableNative.BlakeGCached.native
  helper_model Airbender.Compiler.HelperNative.BlakeGCached.native inputs 112 phase 0

end Airbender.Compiler.CounterFrameNative.BlakeGCached
