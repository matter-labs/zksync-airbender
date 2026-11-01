import Airbender.Import.GKRProtocol.CounterFrameImport
import Airbender.Proofs.GKRProtocol.HelperValidityNative.UnifiedCached
import Airbender.Proofs.GKRProtocol.TableNative.UnifiedCached

namespace Airbender.Compiler.CounterFrameNative.UnifiedCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_counter_frame native from "artifacts/compiler/unified-cached.json"
  base_model Airbender.Compiler.FullArithmeticNative.UnifiedCached.native
  table_model Airbender.Compiler.TableNative.UnifiedCached.native
  helper_model Airbender.Compiler.HelperNative.UnifiedCached.native inputs 137 phase 0

end Airbender.Compiler.CounterFrameNative.UnifiedCached
